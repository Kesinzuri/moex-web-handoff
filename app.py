import ast
import base64
import hashlib
import http.cookiejar
import json
import os
import socket
import ssl
import struct
import subprocess
import threading
import time
import urllib.parse
import urllib.request
import uuid
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timedelta, timezone
from zoneinfo import ZoneInfo

MSK = timezone(timedelta(hours=3))

_SSL_CTX = ssl.create_default_context()


def now_msk():
    return datetime.now(MSK).strftime("%Y-%m-%d %H:%M:%S MSK")

BASE_DIR = os.path.dirname(os.path.abspath(__file__))

ISS_BASE = "https://iss.moex.com/iss"

LK_API_BASE = "https://api.lite-invest.com/api"
LK_LOGIN_PATH = "/auth/local"
LK_BALANCE_PATH = "/moex/trader-data/balance"
LK_USERS_ME = "/users/me"
LK_FIN_RESULT = "/moex/fin-result"
LK_MAX_LOSS = "/moex/max-loss"

INSTRUMENTS = [
    {"secid": "USDRUBF", "title": "USD/RUB", "group": "Валюты", "url": "https://www.moex.com/a8141", "mult": 1000},
    {"secid": "EURRUBF", "title": "EUR/RUB", "group": "Валюты", "url": "https://www.moex.com/a8141", "mult": 1000},
    {"secid": "CNYRUBF", "title": "CNY/RUB", "group": "Валюты", "url": "https://www.moex.com/a8141", "mult": 1000},
    {"secid": "SBERF", "title": "Сбербанк", "group": "Акции", "url": "https://www.moex.com/a8805", "mult": 100},
    {"secid": "GAZPF", "title": "Газпром", "group": "Акции", "url": "https://www.moex.com/a8805", "mult": 100},
    {"secid": "IMOEXF", "title": "Индекс МосБиржи", "group": "Индексы", "url": "https://www.moex.com/a8803", "mult": 10},
    {"secid": "RGBIF", "title": "Индекс RGBI", "group": "Индексы", "url": "https://www.moex.com/a8803", "mult": 100},
    {"secid": "SP500F", "title": "S&P 500", "group": "Индексы", "url": "https://www.moex.com/a9365", "mult": 1},
    {"secid": "QQQF", "title": "QQQ", "group": "Индексы", "url": "https://www.moex.com/a9365", "mult": 1},
    {"secid": "GLDRUBF", "title": "Золото", "group": "Металлы", "url": "https://www.moex.com/a8493", "mult": 1},
    {"secid": "SLVRUBF", "title": "Серебро", "group": "Металлы", "url": "https://www.moex.com/a8493", "mult": 100},
]

FUNDING_SECIDS = {str(it["secid"]) for it in INSTRUMENTS}


def funding_secid_for(isin):
    if not isin:
        return None
    if isin in FUNDING_SECIDS:
        return isin
    return None


PAYOUT_TABLE = [
    (1500000, 0.05),
    (750000, 0.06),
    (400000, 0.07),
    (200000, 0.08),
    (100000, 0.10),
]


def payout_rate(balance):
    if balance is None:
        return None
    for threshold, rate in PAYOUT_TABLE:
        if balance >= threshold:
            return rate
    return 0.20


def snapshot_funding():
    with lock:
        data = state["data"] or []
    out = {}
    for r in data:
        if isinstance(r, dict) and r.get("secid"):
            out[r["secid"]] = r
    return out


TTL = 30
FUND_TTL = 60  # сводка фандингов обновляется каждую минуту
FUND_TTL_MAX = 900  # при устойчивых ошибках интервал растёт до 15 минут
FUND_STALE_TTL = 150  # данные фандингов считаются устаревшими через 2.5 минуты
LK_STALE_TTL = 150  # данные ЛК считаются устаревшими через 2.5 минуты
_fund_backoff = FUND_TTL  # текущий интервал (адаптивный)
state = {"data": None, "updated": None, "error": None, "ts": 0.0}
lock = threading.Lock()
# отдельные локи на источник: сбой/медленность одного API не блокирует остальные
fund_fetch_lock = threading.Lock()
lk_fetch_lock = threading.Lock()
ct_fetch_lock = threading.Lock()
td_fetch_lock = threading.Lock()

LK_TTL = 60
lk_state = {"accounts": {}}
lk_lock = threading.Lock()

TD_API_BASE = "https://api.tradersdiaries.com/prod"
TD_ID_API = "https://id-api.tradersdiaries.com"
TD_CLIENT_ID = "tradersdiaries"
TD_REDIRECT_URI = "https://tradersdiaries.com/diary/"
TD_TTL = 300
TD_STALE_TTL = 360  # данные TD считаются устаревшими через 6 минут
td_state = {"accounts": {}, "updated": None, "error": None, "ts": 0.0}
td_lock = threading.Lock()
td_token = {"access": None, "device_id": None, "exp": 0.0}
_td_opener_ = urllib.request.build_opener(urllib.request.HTTPSHandler(context=_SSL_CTX))
TD_COOKIE_PATH = os.path.join(BASE_DIR, "td_cookies.txt")

BALANCE_HISTORY = os.path.join(BASE_DIR, "balance_history.json")

def load_balance_history():
    if not os.path.exists(BALANCE_HISTORY):
        return {}
    try:
        with open(BALANCE_HISTORY, encoding="utf-8") as f:
            h = json.load(f)
        return h if isinstance(h, dict) else {}
    except Exception:
        return {}

def save_balance_history(h):
    try:
        with open(BALANCE_HISTORY, "w", encoding="utf-8") as f:
            json.dump(h, f, ensure_ascii=False, indent=1)
    except Exception:
        pass

def lk_record_balance(login, balance):
    if balance is None:
        return
    day = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    h = load_balance_history()
    days = h.setdefault(login, {})
    days[day] = round(balance, 2)
    save_balance_history(h)

def lk_yesterday_balance(login):
    h = load_balance_history().get(login, {})
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    prev = [d for d in h if d < today]
    if not prev:
        return None
    return h[max(prev)]


CBR_USD_URL = "https://www.cbr-xml-daily.ru/daily_json.js"
USD_TTL = 3600
usd_cache = {"value": None, "ts": 0}
usd_lock = threading.Lock()
def _read_json(path, default=None):
    """Читает JSON из файла; при отсутствии файла или ошибке парсинга — default."""
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return default


def _write_json(path, obj):
    """Пишет obj в JSON-файл (ensure_ascii=False); ошибки записи игнорируются."""
    try:
        with open(path, "w", encoding="utf-8") as f:
            json.dump(obj, f, ensure_ascii=False)
        return True
    except Exception:
        return False


USD_CACHE_FILE = os.path.join(BASE_DIR, ".usd_cache.json")


def save_usd_cache(v):
    """Сохраняет курс USD в файл, чтобы он переживал перезапуск сервера
    (аналогично .lk_cache.json / .ct_cache.json)."""
    _write_json(USD_CACHE_FILE, {"value": v, "ts": time.time()})


def load_usd_cache():
    return (_read_json(USD_CACHE_FILE) or {}).get("value")


DEALS_PATH = os.path.join(BASE_DIR, "deals.json")

TICKERS_PATH = os.path.join(BASE_DIR, "tickers.json")


def load_tickers_data():
    try:
        with open(TICKERS_PATH, encoding="utf-8") as f:
            d = json.load(f)
        return d
    except Exception:
        return {}


_TICKERS_DATA = load_tickers_data()
TICKERS = _TICKERS_DATA.get("tickers") or {}
DEAL_TYPES = _TICKERS_DATA.get("deal_types") or []

if not DEAL_TYPES:
    DEAL_TYPES = [
        {
            "id": "GD1/XAU",
            "title": "GD1/XAU — золото (MOEX + форекс)",
            "legs": [
                {"key": "GD1", "title": "GD1", "kind": "moex_gold", "defaultSide": "buy", "mult": 1, "unit": "oz"},
                {"key": "GD2", "title": "GD2", "kind": "moex_gold", "defaultSide": "buy", "mult": 1, "unit": "oz"},
                {"key": "XAUUSD", "title": "XAUUSD", "kind": "manual", "defaultSide": "sell", "mult": 100, "unit": "oz"},
            ],
        },
    ]

# активные виды сделок (пользователь выбрал только 2 примера)
ACTIVE_DEAL_TYPES = ["Si1/USDR", "UC1/USDCNH", "ED1/EURUSD", "GD1/XAUUSD"]
DEAL_TYPES = [t for t in DEAL_TYPES if t.get("id") in ACTIVE_DEAL_TYPES] or DEAL_TYPES

DEAL_START_NUM = 1000

GOLD_CONTRACTS_TTL = 60
gold_contracts_cache = {"data": None, "ts": 0}
gold_contracts_lock = threading.Lock()

PRICES_TTL = 60
moex_prices_cache = {"data": None, "ts": 0}
moex_prices_lock = threading.RLock()


def get_usd_rate():
    with usd_lock:
        if usd_cache["value"] is not None and time.time() - usd_cache["ts"] < USD_TTL:
            return usd_cache["value"]
    try:
        data = fetch_json(CBR_USD_URL)
        v = data.get("Valute", {}).get("USD", {}).get("Value")
        if isinstance(v, (int, float)):
            with usd_lock:
                usd_cache["value"] = round(v, 4)
                usd_cache["ts"] = time.time()
            save_usd_cache(usd_cache["value"])
            return usd_cache["value"]
    except Exception:
        pass
    with usd_lock:
        return usd_cache["value"]


def get_usd_rate_cached():
    """Курс USD только из кеша (память + файл), без сетевых запросов."""
    with usd_lock:
        v = usd_cache["value"]
    if v is not None:
        return v
    return load_usd_cache()


usd_date_cache = {}  # 'YYYY-MM-DD' -> курс USD (исторический, ЦБ РФ)
usd_date_lock = threading.Lock()


def get_usd_rate_at(date_str):
    """Курс USD/RUB на дату (архив cbr-xml-daily.ru, fallback: XML cbr.ru)."""
    if not date_str:
        return None
    with usd_date_lock:
        if date_str in usd_date_cache:
            return usd_date_cache[date_str]
    v = None
    try:
        y, m, d = date_str.split("-")
        url = f"https://www.cbr-xml-daily.ru/archive/{y}/{m}/{d}/daily_json.js"
        data = fetch_json(url)
        vv = (data or {}).get("Valute", {}).get("USD", {}).get("Value")
        if isinstance(vv, (int, float)):
            v = round(float(vv), 4)
    except Exception:
        pass
    if v is None:
        try:
            url = f"https://www.cbr.ru/scripts/XML_daily.asp?date_req={m}/{d}/{y}"
            req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
            with urllib.request.urlopen(req, timeout=20, context=_SSL_CTX) as resp:
                html = resp.read().decode("utf-8", "replace")
            import re as _re
            mch = _re.search(r"<CharCode>USD</CharCode>.*?<Value>([\d,]+)</Value>", html, _re.S)
            if mch:
                v = round(float(mch.group(1).replace(",", ".")), 4)
        except Exception:
            v = None
    if v is not None:
        with usd_date_lock:
            usd_date_cache[date_str] = v
    return v


def load_gold_contracts():
    with gold_contracts_lock:
        if gold_contracts_cache["data"] is not None and time.time() - gold_contracts_cache["ts"] < GOLD_CONTRACTS_TTL:
            return gold_contracts_cache["data"]
    try:
        url = (
            f"{ISS_BASE}/engines/futures/markets/forts/securities.json"
            "?iss.meta=off&limit=0&iss.only=securities,marketdata"
        )
        d = fetch_json(url)
        scols = d.get("securities", {}).get("columns", [])
        srows = d.get("securities", {}).get("data", [])
        mcols = d.get("marketdata", {}).get("columns", [])
        mrows = d.get("marketdata", {}).get("data", [])
        si = {c: i for i, c in enumerate(scols)}
        mi = {c: i for i, c in enumerate(mcols)}
        out = []
        prices = {}
        for sr, mr in zip(srows, mrows):
            if si.get("ASSETCODE") is None or len(sr) <= si["ASSETCODE"]:
                continue
            ac = (sr[si["ASSETCODE"]] or "").upper()
            if ac not in ("GOLD", "SI", "EU", "ED", "UCNY", "CNY"):
                continue
            last = mr[mi["LAST"]] if "LAST" in mi and len(mr) > mi["LAST"] else None
            last_rub = mr[mi["LAST_RUB"]] if "LAST_RUB" in mi and len(mr) > mi["LAST_RUB"] else None
            secid = sr[si["SECID"]]
            tradedate = sr[si.get("LASTTRADEDATE")] if si.get("LASTTRADEDATE") is not None and len(sr) > si["LASTTRADEDATE"] else None
            if ac == "GOLD":
                out.append(
                    {
                        "secid": secid,
                        "name": sr[si.get("SHORTNAME", -1)] if si.get("SHORTNAME") is not None and len(sr) > si["SHORTNAME"] else secid,
                        "last": last,
                        "lastRub": last_rub,
                        "tradedate": tradedate,
                    }
                )
            if last is not None and tradedate:
                prices.setdefault(ac, [])
                prices[ac].append((tradedate, last))
        out.sort(key=lambda c: c["tradedate"] or "")
        with gold_contracts_lock:
            gold_contracts_cache["data"] = out
            gold_contracts_cache["ts"] = time.time()
        refresh_moex_prices_cache(prices, {})
        return out
    except Exception:
        with gold_contracts_lock:
            return gold_contracts_cache["data"] or []


def load_moex_prices():
    with moex_prices_lock:
        if moex_prices_cache["data"] is not None and time.time() - moex_prices_cache["ts"] < PRICES_TTL:
            return moex_prices_cache["data"]
    try:
        # futures: one request for currency/gold asset codes
        url = (
            f"{ISS_BASE}/engines/futures/markets/forts/securities.json"
            "?iss.meta=off&limit=0&iss.only=securities,marketdata"
        )
        d = fetch_json(url)
        scols = d.get("securities", {}).get("columns", [])
        srows = d.get("securities", {}).get("data", [])
        mcols = d.get("marketdata", {}).get("columns", [])
        mrows = d.get("marketdata", {}).get("data", [])
        si = {c: i for i, c in enumerate(scols)}
        mi = {c: i for i, c in enumerate(mcols)}
        prices = {}
        for sr, mr in zip(srows, mrows):
            if si.get("ASSETCODE") is None or len(sr) <= si["ASSETCODE"]:
                continue
            ac = (sr[si["ASSETCODE"]] or "").upper()
            if ac not in ("GOLD", "SI", "EU", "ED", "UCNY", "CNY", "USDRUBTOM", "EURRUBTOM", "CNYRUBTOM"):
                continue
            last = mr[mi["LAST"]] if "LAST" in mi and len(mr) > mi["LAST"] else None
            tradedate = sr[si.get("LASTTRADEDATE")] if si.get("LASTTRADEDATE") is not None and len(sr) > si["LASTTRADEDATE"] else None
            if last is not None and tradedate:
                code = {"USDRUBTOM": "USDRUBF", "EURRUBTOM": "EURRUBF", "CNYRUBTOM": "CNYRUBF"}.get(ac, ac)
                prices.setdefault("FUT:" + code, []).append((tradedate, last))

        # spots: currency market
        spot_secids = ["EUR_RUB__TOM", "USD000UTSTOM", "CNYRUB_TOM"]
        for secid in spot_secids:
            try:
                u = f"{ISS_BASE}/engines/currency/markets/selt/securities/{secid}.json?iss.meta=off&iss.only=marketdata"
                s = fetch_json(u)
                mcols2 = (s.get("marketdata") or {}).get("columns", []) or []
                mrows2 = (s.get("marketdata") or {}).get("data", []) or []
                mi2 = {c: i for i, c in enumerate(mcols2)}
                for mr2 in mrows2:
                    last = mr2[mi2["LAST"]] if "LAST" in mi2 and len(mr2) > mi2["LAST"] else None
                    if last is not None:
                        prices["SPOT:" + secid] = ("2099-01-01", last)
                        break
            except Exception:
                continue

        with moex_prices_lock:
            refresh_moex_prices_cache(prices, {})
            moex_prices_cache["data"] = prices
            moex_prices_cache["ts"] = time.time()
        return prices
    except Exception:
        with moex_prices_lock:
            return moex_prices_cache["data"] or {}


def refresh_moex_prices_cache(prices, _extra):
    if prices:
        # приводим к единому формату: фьючерсные ключи — с префиксом FUT:
        norm = {}
        for k, v in prices.items():
            kk = k if (k.startswith("FUT:") or k.startswith("SPOT:")) else "FUT:" + k
            norm[kk] = v
        with moex_prices_lock:
            moex_prices_cache["data"] = norm
            moex_prices_cache["ts"] = time.time()


def best_futures_price(prices, code):
    key = "FUT:" + code.upper()
    items = prices.get(key)
    if not items:
        ac = "GOLD" if code.upper() == "GOLD" else code.upper()
        if ac != code.upper():
            items = prices.get("FUT:" + ac)
    if not items:
        return None
    return items[0][1]


def cached_moex_prices():
    """Читает кэш цен MOEX без сетевых запросов (для HTTP-потоков)."""
    with moex_prices_lock:
        return moex_prices_cache.get("data") or {}


def deal_leg_current(ldef):
    source = ldef.get("source") or ldef.get("kind")
    prices = cached_moex_prices()
    if source == "forts_future":
        return best_futures_price(prices, ldef.get("moex_code") or "")
    if source == "moex_spot":
        secid = ldef.get("moex_code") or ""
        item = prices.get("SPOT:" + secid)
        return item[1] if item else None
    return None


def load_deals():
    if not os.path.exists(DEALS_PATH):
        return []
    try:
        with open(DEALS_PATH, encoding="utf-8") as f:
            d = json.load(f)
        return d if isinstance(d, list) else []
    except Exception:
        return []


def save_deals(deals):
    try:
        with open(DEALS_PATH, "w", encoding="utf-8") as f:
            json.dump(deals, f, ensure_ascii=False, indent=1)
    except Exception:
        pass


def num_or_none(v):
    if v in (None, ""):
        return None
    try:
        return float(str(v).replace(",", "."))
    except ValueError:
        return None


def deal_leg_pnl_pair(leg, leg_def, cur):
    """Return (pnl_in_leg_currency, entry, current)."""
    if not isinstance(leg, dict):
        return None, None, None
    current = leg.get("current")
    entry = leg.get("entry")
    qty = leg.get("qty")
    if current in (None, "") or entry in (None, "") or qty in (None, ""):
        return None, num_or_none(entry), num_or_none(current)
    current, entry, qty = num_or_none(current), num_or_none(entry), num_or_none(qty)
    if None in (current, entry, qty):
        return None, entry, current
    mult = (leg_def or {}).get("mult") or 1
    div = (leg_def or {}).get("div") or 1
    side = (leg.get("side") or (leg_def or {}).get("defaultSide") or "buy").lower()
    sign = 1 if side == "buy" else -1
    pnl = sign * (current / div - entry) * qty * mult
    return round(pnl, 2), entry, current


def deal_leg_currency(ldef):
    src = ldef.get("source") or ldef.get("kind")
    if src in ("fx", "manual"):
        return "usd"
    if ldef.get("cur"):
        return ldef.get("cur")
    return "rub"


def deal_next_id(deals):
    """Новый номер сделки: от DEAL_START_NUM вверх по существующим."""
    ids = [d.get("id") for d in deals if isinstance(d.get("id"), int)]
    return max([DEAL_START_NUM - 1] + ids) + 1


def create_deal(type_id):
    """Создаёт новую сделку: номер от 1000, статус «Активна», ноги из типа."""
    t = next((x for x in DEAL_TYPES if x.get("id") == type_id), None)
    if not t:
        return None
    deal = {
        "id": deal_next_id(load_deals()),
        "typeId": type_id,
        "status": "Активна",
        "openedAt": datetime.now(MSK).date().isoformat(),
        "closedAt": None,
        "legs": [],
    }
    for ld in (t.get("legs") or []):
        kind = "forex" if (ld.get("source") in ("fx", "manual") or ld.get("kind") == "manual") else "moex"
        deal["legs"].append({
            "key": ld.get("key"),
            "kind": kind,
            "side": ld.get("defaultSide") or "buy",
            "positions": [],
        })
    deals = load_deals()
    deals.append(deal)
    save_deals(deals)
    # авто-привязка открытых непривязанных позиций по типу сделки
    try:
        auto_bind_deal(deal)
    except Exception:
        pass
    return deal


def deal_leg_match(ld, src, isin, symbol):
    """Позиция (src=lk/ct, isin/symbol) подходит к ноге типа сделки ld."""
    if not isinstance(ld, dict):
        return False
    lsrc = ld.get("source") or ld.get("kind")
    if src == "ct":
        if lsrc not in ("fx", "manual"):
            return False
        target = (ld.get("ticker") or ld.get("key") or "").upper()
        return bool(target) and (symbol or "").upper().startswith(target)
    if lsrc not in ("forts_future", "moex_spot", "moex_gold"):
        return False
    code = (ld.get("moex_code") or "").upper()
    iu = (isin or "").upper()
    return bool(code) and (iu == code or iu.startswith(code + "-") or iu.startswith(code + "/"))


def bind_position(deal_id, src, isin=None, symbol=None, login=None, account=None):
    """Привязывает позицию (MOEX: src=lk + isin/login/account; Forex: src=ct + symbol)
    к подходящей ноге сделки. Авто-выбор ноги по инструменту."""
    deals = load_deals()
    d = next((x for x in deals if x.get("id") == deal_id), None)
    if not d:
        return {"ok": False, "error": "Сделка не найдена"}
    t = next((x for x in DEAL_TYPES if x.get("id") == d.get("typeId")), None)
    if not t:
        return {"ok": False, "error": "Тип сделки не найден"}
    reopened = False
    if d.get("status") == "Закрыта":
        d["status"] = "Активна"
        d["closedAt"] = None
        d["pnlRub"] = None
        d["entryPoint"] = None
        d["exitPoint"] = None
        for leg in d.get("legs") or []:
            for pos in leg.get("positions") or []:
                for k in ("savedPnl", "savedEntry", "savedCurrent", "savedQty"):
                    pos.pop(k, None)
    key = (symbol or isin or "").upper()
    for leg in d.get("legs") or []:
        ld = next((x for x in (t.get("legs") or []) if x.get("key") == leg.get("key")), {})
        if not deal_leg_match(ld, src, isin, symbol):
            continue
        pos = next((p for p in (leg.get("positions") or []) if (p.get("symbol") or p.get("isin") or "").upper() == key), None)
        if pos:
            return {"ok": False, "error": "Позиция уже привязана к этой сделке"}
        if len(leg.get("positions") or []) >= 2:
            return {"ok": False, "error": "В ноге уже 2 позиции"}
        p = {"src": src, "isin": isin, "symbol": symbol}
        if src == "lk":
            p["login"] = login
            p["account"] = account
        leg.setdefault("positions", []).append(p)
        save_deals(deals)
        return {"ok": True}
    return {"ok": False, "error": "Нет подходящей ноги для этого инструмента"}


def unbind_position(deal_id, src, isin=None, symbol=None):
    """Отвязывает позицию от всех ног сделки."""
    deals = load_deals()
    d = next((x for x in deals if x.get("id") == deal_id), None)
    if not d:
        return {"ok": False, "error": "Сделка не найдена"}
    key = (symbol or isin or "").upper()
    changed = False
    for leg in d.get("legs") or []:
        before = len(leg.get("positions") or [])
        leg["positions"] = [p for p in (leg.get("positions") or [])
                            if (p.get("symbol") or p.get("isin") or "").upper() != key or p.get("src") != src]
        if len(leg.get("positions") or []) != before:
            changed = True
    if changed:
        save_deals(deals)
    return {"ok": True}


def iter_open_positions():
    """Возвращает список открытых позиций из lk_state/ct_state.
    Каждая запись: (src, isin_or_symbol, login, account)."""
    result = []
    with lk_lock:
        lk_accs = dict(lk_state.get("accounts") or {})
    for login, st in lk_accs.items():
        data = st.get("data") or {}
        positions = data.get("positions") or {}
        for account, acc_pos in positions.items():
            if not isinstance(acc_pos, dict):
                continue
            for grp in ("futures", "actions", "currency"):
                for it in (acc_pos.get(grp) or []):
                    if not isinstance(it, dict):
                        continue
                    isin = it.get("isin")
                    qty = num_or_none(it.get("position"))
                    if not isin or qty in (None, 0):
                        continue
                    result.append(("lk", isin, login, account))
    with ct_lock:
        ct_accs = dict(ct_state.get("accounts") or {})
    for label, st in ct_accs.items():
        data = st.get("data") or {}
        for a in (data.get("accounts") or []):
            for p in (a.get("positions") or []):
                if not isinstance(p, dict):
                    continue
                symbol = p.get("symbol")
                qty = num_or_none(p.get("volumeUnits")) or num_or_none(p.get("pos"))
                if not symbol or qty in (None, 0):
                    continue
                result.append(("ct", symbol, None, None))
    return result


def auto_bind_deal(deal):
    """Автоматически привязывает открытые непривязанные позиции к ногам сделки.
    Для каждой ноги ищет первую подходящую открытую позицию (по deal_leg_match),
    ещё не привязанную ни к одной сделке."""
    t = next((x for x in DEAL_TYPES if x.get("id") == deal.get("typeId")), None)
    if not t:
        return
    bound = set()
    for leg in deal.get("legs") or []:
        for p in leg.get("positions") or []:
            key = (
                p.get("src"),
                (p.get("symbol") or p.get("isin") or "").upper(),
                (p.get("login") or "").lower(),
                (p.get("account") or "").lower(),
            )
            bound.add(key)
    open_pos = iter_open_positions()
    for ld in (t.get("legs") or []):
        leg = next((x for x in deal.get("legs") or [] if x.get("key") == ld.get("key")), None)
        if not leg:
            continue
        for op in open_pos:
            src, isin, login, account = op
            iu = isin if src == "lk" else None
            sym = isin if src == "ct" else None
            if not deal_leg_match(ld, src, iu, sym):
                continue
            key = (src, (isin or "").upper(), (login or "").lower(), (account or "").lower())
            if key in bound:
                continue
            bind_position(deal["id"], src, isin=iu, symbol=sym, login=login, account=account)
            bound.add(key)
            break


def auto_bind_all():
    """Привязывает открытые позиции к активным сделкам без привязанных позиций
    (используется при старте, чтобы подхватить сделки, созданные до появления
    авто-привязки). Затрагивает только сделки, у которых вообще нет позиций."""
    deals = load_deals()
    # собираем уже привязанные позиции, чтобы не дублировать
    taken = set()
    for d in deals:
        for leg in d.get("legs") or []:
            for p in leg.get("positions") or []:
                taken.add((
                    p.get("src"),
                    (p.get("symbol") or p.get("isin") or "").upper(),
                    (p.get("login") or "").lower(),
                    (p.get("account") or "").lower(),
                ))
    # только активные сделки без единой позиции; от самой свежей к старой
    candidates = [d for d in deals if d.get("status") != "Закрыта"
                  and sum(len(leg.get("positions") or []) for leg in d.get("legs") or []) == 0]
    candidates.sort(key=lambda d: d.get("id") or 0, reverse=True)
    for d in candidates:
        open_pos = iter_open_positions()
        for op in open_pos:
            src, isin, login, account = op
            key = (src, (isin or "").upper(), (login or "").lower(), (account or "").lower())
            if key in taken:
                continue
            t = next((x for x in DEAL_TYPES if x.get("id") == d.get("typeId")), None)
            if not t:
                continue
            matched = False
            for ld in (t.get("legs") or []):
                iu = isin if src == "lk" else None
                sym = isin if src == "ct" else None
                if deal_leg_match(ld, src, iu, sym):
                    matched = True
                    break
            if not matched:
                continue
            bind_position(d["id"], src, isin=iu, symbol=sym, login=login, account=account)
            taken.add(key)


def close_deal(deal_id):
    """Закрывает сделку (статус «Закрыта», closedAt) с фиксацией итогового результата."""
    deals = load_deals()
    d = next((x for x in deals if x.get("id") == deal_id), None)
    if not d:
        return {"ok": False, "error": "Сделка не найдена"}
    if d.get("status") != "Активна":
        return {"ok": False, "error": "Сделка уже закрыта"}
    # Обогащаем сделку живыми данными ПЕРЕД закрытием — так PnL позиций
    # фиксируется, пока они ещё доступны в источниках (особенно важно для CT/Forex,
    # где позиция может исчезнуть из API после закрытия сделки)
    try:
        enrich_deals([d])
    except Exception:
        pass
    # Если позиции уже имеют значения PnL (от страницы), сохраняем их
    # перед закрытием — freeze_deal_result использует live=True с
    # приоритетом существующим значениям pos["pnl"]
    d["status"] = "Закрыта"
    d["closedAt"] = datetime.now(MSK).date().isoformat()
    freeze_deal_result(d)
    save_deals(deals)
    return {"ok": True}


def eval_formula(formula, values):
    """Evaluate a simple arithmetic formula with named variables (SI1, USDRUBF, ...)."""
    if not formula:
        return None
    values = {k.upper(): v for k, v in (values or {}).items()}
    if any(v is None for v in values.values()):
        return None

    def _ev(node):
        if isinstance(node, ast.Expression):
            return _ev(node.body)
        if isinstance(node, ast.Constant):
            return node.value
        if isinstance(node, ast.Name):
            return values.get(node.id.upper())
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -_ev(node.operand)
        if isinstance(node, ast.BinOp):
            op = {
                ast.Add: lambda a, b: a + b,
                ast.Sub: lambda a, b: a - b,
                ast.Mult: lambda a, b: a * b,
                ast.Div: lambda a, b: (a / b) if b else None,
            }.get(type(node.op))
            if op is None:
                return None
            return op(_ev(node.left), _ev(node.right))
        return None

    try:
        res = _ev(ast.parse(formula, mode="eval"))
        return None if res is None else float(res)
    except Exception:
        return None


def lk_position_resolve(login, account, isin):
    """Ищет позицию в lk_state по (login, account, isin).
    Возвращает (qty, entry, current, pnl_rub, data_ok) или None.
    data_ok=False — данные по этому ЛК-логину ещё не загружены (не путать с закрытой позицией)."""
    with lk_lock:
        st = (lk_state.get("accounts") or {}).get(login)
    if not st or not (st.get("data") or {}):
        # попробуем кэш-файл
        cache = load_lk_cache()
        if cache:
            for a in (cache.get("accounts") or []):
                if (a.get("login") or "").lower() != (login or "").lower():
                    continue
                data = a.get("data") or {}
                positions = data.get("positions") or {}
                acc_pos = positions.get(account)
                if isinstance(acc_pos, dict):
                    for grp in ("futures", "actions", "currency"):
                        for it in (acc_pos.get(grp) or []):
                            if not isinstance(it, dict):
                                continue
                            if (it.get("isin") or "").upper() != (isin or "").upper():
                                continue
                            qty = num_or_none(it.get("position"))
                            if qty in (None, 0):
                                pnl = num_or_none(it.get("finance_result"))
                                return None, None, it.get("snapshot_price"), pnl, True
                            tp = num_or_none(it.get("total_price"))
                            lot = num_or_none(it.get("in_lot")) or 1
                            entry = (tp / (abs(qty) * lot)) if tp not in (None, 0) else None
                            cur = it.get("snapshot_price")
                            pnl = num_or_none(it.get("finance_result"))
                            return qty, entry, cur, pnl, True
                    return None, None, None, None, True  # account found, position not found
            return None, None, None, None, True  # login found, but position not found
    data = st.get("data") or {}
    positions = data.get("positions") or {}
    acc_pos = positions.get(account)
    if not isinstance(acc_pos, dict):
        return None, None, None, None, True
    for grp in ("futures", "actions", "currency"):
        for it in (acc_pos.get(grp) or []):
            if not isinstance(it, dict):
                continue
            if (it.get("isin") or "").upper() != (isin or "").upper():
                continue
            qty = num_or_none(it.get("position"))
            if qty in (None, 0):
                # позиция закрыта: возвращаем итог (finance_result) как pnl, qty=None
                # но если кэш имеет позицию открытой — используем кэш (она более свежая
                # по отношению к закрытию позиции в ЛК)
                cache = load_lk_cache()
                if cache:
                    for a in (cache.get("accounts") or []):
                        if (a.get("login") or "").lower() != (login or "").lower():
                            continue
                        cache_data = a.get("data") or {}
                        cache_positions = cache_data.get("positions") or {}
                        cache_acc = cache_positions.get(account)
                        if not isinstance(cache_acc, dict):
                            continue
                        for cgrp in ("futures", "actions", "currency"):
                            for cp in (cache_acc.get(cgrp) or []):
                                if not isinstance(cp, dict):
                                    continue
                                if (cp.get("isin") or "").upper() != (isin or "").upper():
                                    continue
                                cache_qty = num_or_none(cp.get("position"))
                                if cache_qty not in (None, 0):
                                    # кэш имеет позицию открытой — используем её данные
                                    tp = num_or_none(cp.get("total_price"))
                                    lot = num_or_none(cp.get("in_lot")) or 1
                                    cache_entry = (tp / (abs(cache_qty) * lot)) if tp not in (None, 0) else None
                                    cache_cur = cp.get("snapshot_price")
                                    cache_pnl = num_or_none(cp.get("finance_result"))
                                    return cache_qty, cache_entry, cache_cur, cache_pnl, True
                                # кэш тоже закрыта — используем кэш finance_result
                                cache_pnl = num_or_none(cp.get("finance_result"))
                                if cache_pnl is not None:
                                    return None, None, cp.get("snapshot_price"), cache_pnl, True
                                break
                            break
                        break
                # закрытая позиция, нет кэша — возвращаем live данные
                pnl = num_or_none(it.get("finance_result"))
                return None, None, it.get("snapshot_price"), pnl, True
            tp = num_or_none(it.get("total_price"))
            lot = num_or_none(it.get("in_lot")) or 1
            entry = (tp / (abs(qty) * lot)) if tp not in (None, 0) else None
            cur = it.get("snapshot_price")
            if cur in (None, ""):
                secid = isin_to_secid(isin)
                cur = get_cached_forts_price(secid) if secid else None
            pnl = num_or_none(it.get("finance_result"))
            return qty, entry, cur, pnl, True
    return None, None, None, None, True


def load_lk_cache():
    """Load LK cache from file."""
    cache_path = LK_CACHE_FILE if os.path.exists(LK_CACHE_FILE) else "/tmp/lk.json"
    if not os.path.exists(cache_path):
        for p in ("/tmp/lk.json", "/tmp/lk_fixed.json"):
            if os.path.exists(p):
                cache_path = p
                break
    if not cache_path or not os.path.exists(cache_path):
        return None
    return _read_json(cache_path)


def load_ct_cache():
    """Load CT cache entries from file."""
    cache_path = CT_CACHE_FILE if os.path.exists(CT_CACHE_FILE) else "/tmp/ct.json"
    if not os.path.exists(cache_path):
        return None
    raw = _read_json(cache_path)
    if raw is None:
        return None
    return raw.get("entries") or []


def ct_sym_base(s):
    """Нормализует имя символа для сопоставления: верхний регистр и отсечение
    суффикса аккаунта/лейбла вида SYMBOL_XP (в сделках хранится 'XAUUSD_xp')."""
    s = (s or "").upper()
    if "_" in s:
        s = s.split("_")[0]
    return s


def ct_position_resolve(symbol):
    """Ищет позицию в ct_state по symbol. Возвращает (qty, entry, current, pnl_rub, data_ok) или None.
    data_ok=False — cTrader-данные ещё не загружены."""
    target = ct_sym_base(symbol)
    with ct_lock:
        snapshot = dict(ct_state.get("accounts") or {})
    if not snapshot:
        # попробуем загрузить из кэш-файла
        cache = load_ct_cache()
        if cache:
            snapshot = {e["label"]: {"data": e.get("data")} for e in cache}
    if not snapshot:
        return None, None, None, None, False
    for label, st in snapshot.items():
        data = (st or {}).get("data") or {}
        for acc in (data.get("accounts") or []):
            for p in (acc.get("positions") or []):
                if not isinstance(p, dict):
                    continue
                if ct_sym_base(p.get("symbol")) != target:
                    continue
                qty = num_or_none(p.get("volumeUnits"))
                if qty in (None, 0):
                    return None, None, None, None, True
                if p.get("side") == "sell":
                    qty = -qty
                return qty, p.get("price"), p.get("price"), _ct_pnl(p), True
    # позиция не найдена в живых данных — попробуем кэш-файл
    cache = load_ct_cache()
    if cache:
        for e in cache:
            data = (e or {}).get("data") or {}
            for acc in (data.get("accounts") or []):
                for p in (acc.get("positions") or []):
                    if not isinstance(p, dict):
                        continue
                    if ct_sym_base(p.get("symbol")) != target:
                        continue
                    qty = num_or_none(p.get("volumeUnits"))
                    if qty in (None, 0):
                        return None, None, None, None, True
                    if p.get("side") == "sell":
                        qty = -qty
                    return qty, p.get("price"), p.get("price"), _ct_pnl(p), True
    return None, None, None, None, True


def _ct_pnl(p):
    """P&L форекс-позиции в долларах США (native валюта cTrader).
    Используем netPnl, при его отсутствии — pnlRub (в наших кэшах это тоже
    долларовое значение). Перевод в рубли выполняется при агрегации сделки."""
    if not isinstance(p, dict):
        return None
    v = p.get("netPnl")
    if v is None:
        v = p.get("pnlRub")
    return num_or_none(v)


def deal_default_commission(d):
    """Комиссия по умолчанию = сумма финрезов MOEX-позиций сделки × payout счёта.
    Форекс (src=ct) не учитывается — там комиссия уже встроена в результат."""
    total = 0.0
    found = False
    for leg in d.get("legs") or []:
        for pos in leg.get("positions") or []:
            if pos.get("src") != "lk":
                continue
            pnl = num_or_none(pos.get("pnl"))
            if pnl is None:
                continue
            payout = None
            with lk_lock:
                st = (lk_state.get("accounts") or {}).get(pos.get("login"))
                if st:
                    payout = (st.get("data") or {}).get("payout")
            if payout is None:
                continue
            total += pnl * payout
            found = True
    return round(total, 2) if found else None


def deal_set_commission(deal_id, commission):
    """Задаёт комиссию по сделке вручную (рубли). Только для закрытой сделки."""
    deals = load_deals()
    d = next((x for x in deals if x.get("id") == deal_id), None)
    if not d:
        return {"ok": False, "error": "Сделка не найдена"}
    if d.get("status") != "Закрыта":
        return {"ok": False, "error": "Комиссию можно задать только после закрытия сделки"}
    if commission is None:
        return {"ok": False, "error": "Укажите комиссию в рублях"}
    try:
        commission = float(commission)
    except Exception:
        return {"ok": False, "error": "Комиссия должна быть числом"}
    d["commission"] = round(commission, 2)
    try:
        snap = enrich_deals([d])[0]
        d["pnlRub"] = snap.get("pnlRub")
    except Exception:
        pass
    save_deals(deals)
    return {"ok": True, "deal": d}


def freeze_deal_result(d):
    """Фиксирует текущий расчёт (pnl по позициям/ногам, точка входа, комиссия) в сделке,
    чтобы итог сохранялся после закрытия, когда позиции исчезнут из данных биржи.
    Снимает снапшот с живых данных (live=True), невзирая на статус сделки."""
    try:
        snap = enrich_deals([d], live=True)[0]
    except Exception:
        return
    d["pnlRub"] = snap.get("pnlRub")
    d["entryPoint"] = snap.get("entryPoint")
    d["exitPoint"] = snap.get("exitPoint")
    if d.get("commission") is None:
        d["commission"] = deal_default_commission(snap)
    src_legs = snap.get("legs") or []
    for leg in d.get("legs") or []:
        sleg = next((x for x in src_legs if x.get("key") == leg.get("key")), {})
        leg["pnlRub"] = sleg.get("pnlRub")
        leg["avgEntry"] = sleg.get("avgEntry")
        leg["current"] = sleg.get("current")
        for pos in leg.get("positions") or []:
            spos = next((x for x in (sleg.get("positions") or [])
                         if (x.get("symbol") or x.get("isin") or "").upper() == (pos.get("symbol") or pos.get("isin") or "").upper()
                         and x.get("src") == pos.get("src")), {})
            pos["savedPnl"] = spos.get("pnl")
            pos["savedEntry"] = spos.get("entry")
            pos["savedCurrent"] = spos.get("current")
            pos["savedQty"] = spos.get("qty")


def enrich_deals(deals, live=False):
    """Обогащает сделки данными источников. live=True — принудительно считать от живых
    данных (используется при фиксации результата перед закрытием). Иначе закрытые сделки
    показывают только зафиксированный итог, без пересчёта от текущего рынка."""
    type_map = {t["id"]: t for t in DEAL_TYPES}
    deals_out = []
    for deal in deals:
        d = deal
        t = type_map.get(d.get("typeId"))
        legs_def = {l["key"]: l for l in (t.get("legs") if t else [])}
        # курс USD для перевода P&L форекс-позиций (в долларах) в рубли:
        # для закрытой сделки — на дату закрытия, иначе — текущий
        usd_rate = None
        if d.get("status") == "Закрыта":
            usd_rate = get_usd_rate_at(d.get("closedAt"))
        if usd_rate in (None, 0):
            usd_rate = get_usd_rate_cached()

        def usd_to_rub(v, src):
            if v is None or src != "ct" or not usd_rate:
                return v
            return v * usd_rate

        deal_pnl_rub = 0.0
        any_pnl = False
        total_entry_rub = 0.0
        all_positions_closed = True
        has_positions = False
        for leg in d.get("legs") or []:
            if not isinstance(leg, dict):
                continue
            ldef = legs_def.get(leg.get("key")) or {}
            leg_pnl_rub = 0.0
            leg_any = False
            leg_avg_num = 0.0
            leg_avg_den = 0.0
            leg_cur = None
            leg_closed = True
            for pos in leg.get("positions") or []:
                if not isinstance(pos, dict):
                    continue
                has_positions = True
                src = pos.get("src")
                if live and pos.get("pnl") is not None:
                    # live=True (freeze): если позиция уже имеет PnL (со страницы),
                    # используем его — не перезапрашиваем у источника
                    info = None
                elif not live and d.get("status") == "Закрыта":
                    # закрытая сделка — только зафиксированный итог, живые данные не пересчитываем
                    info = None
                elif src == "ct":
                    info = ct_position_resolve(pos.get("symbol"))
                else:
                    info = lk_position_resolve(pos.get("login"), pos.get("account"), pos.get("isin"))
                if info is None:
                    # позиция закрыта/исчезла из данных — используем зафиксированный итог, если есть
                    pos["closed"] = True
                    pos["qty"] = pos.get("savedQty") or 0
                    entry = pos.get("savedEntry") or pos.get("entry")
                    cur = pos.get("savedCurrent") or pos.get("current")
                    pnl = pos.get("savedPnl") or pos.get("pnl")
                    pos["entry"] = entry
                    pos["current"] = cur
                    pos["pnl"] = pnl
                    if entry is not None:
                        qty_v = abs(pos.get("savedQty") or pos.get("qty") or 1)
                        leg_avg_num += entry * qty_v
                        leg_avg_den += qty_v
                    if cur is not None:
                        leg_cur = cur
                    if pnl is not None:
                        leg_pnl_rub += usd_to_rub(pnl, src)
                        leg_any = True
                    continue
                    if pos.get("savedPnl") is not None:
                        leg_pnl_rub += pos["savedPnl"]
                        leg_any = True
                    continue

                qty, entry, cur, pnl, data_ok = info

                if not data_ok:
                    # данные источника ещё не загружены — не считаем закрытой,
                    # но для уже закрытой сделки показываем зафиксированный итог
                    if d.get("status") == "Закрыта" and pos.get("savedPnl") is not None:
                        pos["closed"] = True
                        pos["qty"] = pos.get("savedQty") or 0
                        pos["entry"] = pos.get("savedEntry")
                        pos["current"] = pos.get("savedCurrent")
                        pos["pnl"] = pos.get("savedPnl")
                        if pos.get("savedEntry") is not None:
                            qty_v = abs(pos.get("savedQty") or 1)
                            leg_avg_num += pos["savedEntry"] * qty_v
                            leg_avg_den += qty_v
                        if pos.get("savedCurrent") is not None:
                            leg_cur = pos["savedCurrent"]
                        if pos.get("savedPnl") is not None:
                            leg_pnl_rub += pos["savedPnl"]
                            leg_any = True
                        continue
                    # live=True (freeze): если есть текущие значения позиции — используем их
                    if live and (pos.get("pnl") is not None or pos.get("entry") is not None):
                        pos["closed"] = False
                        pos["qty"] = pos.get("qty")
                        pos["entry"] = pos.get("entry")
                        pos["current"] = pos.get("current")
                        pos["pnl"] = pos.get("pnl")
                        if pos.get("pnl") is not None:
                            leg_pnl_rub += usd_to_rub(pos["pnl"], src)
                            leg_any = True
                        if pos.get("entry") is not None:
                            leg_avg_num += pos["entry"] * abs(pos.get("qty") or 0)
                            leg_avg_den += abs(pos.get("qty") or 0)
                        if pos.get("current") is not None:
                            leg_cur = pos["current"]
                        continue
                    pos["closed"] = False
                    if live:
                        # live=True (freeze): сохраняем текущие значения позиции,
                        # если свежие данные недоступны — используем существующие
                        pos["qty"] = pos.get("qty")
                        pos["entry"] = pos.get("entry")
                        pos["current"] = pos.get("current")
                        pos["pnl"] = pos.get("pnl")
                        if pos.get("pnl") is not None:
                            leg_pnl_rub += usd_to_rub(pos["pnl"], src)
                            leg_any = True
                        if pos.get("entry") is not None:
                            leg_avg_num += pos["entry"] * abs(pos.get("qty") or 0)
                            leg_avg_den += abs(pos.get("qty") or 0)
                        if pos.get("current") is not None:
                            leg_cur = pos["current"]
                    else:
                        pos["qty"] = None
                        pos["entry"] = None
                        pos["current"] = None
                        pos["pnl"] = None
                    leg_closed = False
                    continue
                pos["closed"] = qty is None
                pos["qty"] = qty if qty is not None else 0
                if qty is None:
                    # позиция закрыта — приоритет: savedPnl (из сделки) > pos["pnl"] (из deals.json) > live finance_result
                    if pos.get("pnl") is not None:
                        # позиция уже имеет PnL из сделки — используем его
                        pnl = pos.get("pnl")
                        entry = pos.get("entry")
                        cur = pos.get("current")
                    elif pos.get("savedPnl") is not None:
                        pnl = pos.get("savedPnl")
                        entry = pos.get("savedEntry")
                        cur = pos.get("savedCurrent")
                    if live and pnl is None:
                        # live=True (freeze): если свежие данные не дали pnl,
                        # используем ранее обогруженное значение (pos["pnl"])
                        pnl = pos.get("pnl")
                        entry = pos.get("entry")
                        cur = pos.get("current")
                    pos["entry"] = entry
                    pos["current"] = cur
                    pos["pnl"] = pnl
                    if entry is not None:
                        qty_v = abs(pos.get("savedQty") or 1)
                        leg_avg_num += entry * qty_v
                        leg_avg_den += qty_v
                    if cur is not None:
                        leg_cur = cur
                    if pnl is not None:
                        leg_pnl_rub += usd_to_rub(pnl, src)
                        leg_any = True
                    continue
                pos["entry"] = entry
                pos["current"] = cur
                pos["pnl"] = pnl
                leg_closed = False
                if entry is not None:
                    leg_avg_num += entry * abs(qty)
                    leg_avg_den += abs(qty)
                if cur is not None:
                    leg_cur = cur
                if pnl is not None:
                    leg_pnl_rub += usd_to_rub(pnl, src)
                    leg_any = True
            leg["pnlRub"] = round(leg_pnl_rub, 2) if leg_any else None
            leg["avgEntry"] = round(leg_avg_num / leg_avg_den, 4) if leg_avg_den else None
            leg["current"] = leg_cur
            leg["closed"] = leg_closed if (leg.get("positions")) else False
            if not leg_closed:
                all_positions_closed = False
            if leg_any:
                any_pnl = True
                deal_pnl_rub += leg_pnl_rub
        d["pnlRub"] = round(deal_pnl_rub, 2) if any_pnl else None
        d["allClosed"] = all_positions_closed and any(d.get("legs") or []) and has_positions
        # точка входа сделки: отношение средних цен входа ног по формуле вида
        leg_avg = {leg.get("key"): leg.get("avgEntry") for leg in (d.get("legs") or []) if isinstance(leg, dict)}
        leg_cur = {leg.get("key"): leg.get("current") for leg in (d.get("legs") or []) if isinstance(leg, dict)}
        entry_point = None
        exit_point = None
        ratio = (t or {}).get("ratio") or {}
        if ratio.get("formula"):
            _ep = eval_formula(ratio["formula"], leg_avg)
            entry_point = round(_ep, 4) if _ep is not None else None
        elif ratio.get("num") and ratio.get("den"):
            num = leg_avg.get(ratio["num"])
            den = leg_avg.get(ratio["den"])
            if num is not None and den:
                entry_point = round(num / den, 4)
        if ratio.get("formula"):
            _xp = eval_formula(ratio["formula"], leg_cur)
            exit_point = round(_xp, 4) if _xp is not None else None
        elif ratio.get("num") and ratio.get("den"):
            num = leg_cur.get(ratio["num"])
            den = leg_cur.get(ratio["den"])
            if num is not None and den:
                exit_point = round(num / den, 4)
        d["entryPoint"] = entry_point
        d["exitPoint"] = exit_point
        # авто-закрытие: все привязанные позиции закрыты
        if d.get("status") == "Активна" and d.get("allClosed"):
            d["status"] = "Закрыта"
            d["closedAt"] = d.get("closedAt") or datetime.now(MSK).date().isoformat()
            try:
                freeze_deal_result(d)
            except Exception:
                pass
        deals_out.append(d)
    return deals_out


def deal_stats(deals):
    """Итоги: за сегодня/вчера/неделю/месяц + по типам."""
    today = datetime.now(MSK).date().isoformat()
    yesterday = (datetime.now(MSK).date() - timedelta(days=1)).isoformat()
    week_ago = (datetime.now(MSK).date() - timedelta(days=7)).isoformat()
    month_ago = (datetime.now(MSK).date() - timedelta(days=30)).isoformat()

    by_day = {}
    by_type = {}
    open_pnl = 0.0
    closed_count = 0

    for d in deals:
        pnl = num_or_none(d.get("pnlRub"))
        if pnl is None:
            continue
        day = (d.get("closedAt") or d.get("openedAt") or today)[:10]
        by_day[day] = by_day.get(day, 0.0) + pnl
        tid = d.get("typeId") or "?"
        by_type[tid] = by_type.get(tid, 0.0) + pnl
        if d.get("status") == "Закрыта" and d.get("closedAt"):
            closed_count += 1
        if d.get("status") != "Закрыта":
            open_pnl += pnl

    today_pnl = 0.0
    week_pnl = 0.0
    month_pnl = 0.0
    for d in deals:
        pnl = num_or_none(d.get("pnlRub"))
        if pnl is None:
            continue
        if d.get("status") == "Закрыта":
            day = (d.get("closedAt") or today)[:10]
        else:
            day = today
        if day == today:
            today_pnl += pnl
        if day >= week_ago:
            week_pnl += pnl
        if day >= month_ago:
            month_pnl += pnl

    yesterday_pnl = by_day.get(yesterday, 0.0)
    day_rows = [{"date": k, "pnl": round(v, 2)} for k, v in sorted(by_day.items())]
    type_rows = [
        {"typeId": tid, "title": next((t["title"] for t in DEAL_TYPES if t["id"] == tid), tid), "pnl": round(v, 2)}
        for tid, v in sorted(by_type.items())
    ]
    return {
        "today": round(today_pnl, 2),
        "yesterday": round(yesterday_pnl, 2),
        "week": round(week_pnl, 2),
        "month": round(month_pnl, 2),
        "open": round(open_pnl, 2),
        "closedCount": closed_count,
        "byDay": day_rows,
        "byType": type_rows,
    }


_forts_price_cache = {}  # secid → (ts, price)
_forts_price_lock = threading.Lock()
FORTS_PRICE_TTL = 300  # 5 min


def get_forts_price(secid, force=False):
    """Возвращает LAST или SETTLEPRICE для конкретного фьючерса по secid."""
    now = time.time()
    with _forts_price_lock:
        if not force and secid in _forts_price_cache:
            ts, p = _forts_price_cache[secid]
            if now - ts < FORTS_PRICE_TTL:
                return p
    try:
        url = (
            f"{ISS_BASE}/engines/futures/markets/forts/securities/{secid}.json"
            "?iss.meta=off&iss.only=securities,marketdata"
        )
        d = fetch_json(url, timeout=10)
        mc = d.get("marketdata", {}).get("columns", [])
        mr = d.get("marketdata", {}).get("data", [])
        mi = {c: i for i, c in enumerate(mc)}
        price = None
        if mr:
            row = mr[0]
            price = row[mi["LAST"]] if "LAST" in mi else None
            if price is None:
                price = row[mi["SETTLEPRICE"]] if "SETTLEPRICE" in mi else None
        with _forts_price_lock:
            _forts_price_cache[secid] = (now, price)
        return price
    except Exception:
        return None


_stock_prev_cache = {}  # secid → (ts, prev_close)
_stock_prev_lock = threading.Lock()
STOCK_PREV_TTL = 21600  # 6 h — меняется раз в день после ночного клиринга 23:50


def get_cached_forts_price(secid):
    """Возвращает кэшированную цену фьючерса без сетевых запросов (для HTTP-потоков)."""
    with _forts_price_lock:
        if secid in _forts_price_cache:
            ts, p = _forts_price_cache[secid]
            if time.time() - ts < FORTS_PRICE_TTL:
                return p
    return None


def get_stock_prev_close(secid):
    """Возвращает PREVPRICE (цена по итогам предыдущего дня, после ночного клиринга) для акции."""
    now = time.time()
    with _stock_prev_lock:
        if secid in _stock_prev_cache:
            ts, p = _stock_prev_cache[secid]
            if now - ts < STOCK_PREV_TTL:
                return p
    try:
        url = (
            f"{ISS_BASE}/engines/stock/markets/shares/securities/{secid}.json"
            "?iss.meta=off&iss.only=securities"
        )
        d = fetch_json(url, timeout=10)
        sc = d.get("securities", {}).get("columns", [])
        sr = d.get("securities", {}).get("data", [])
        si = {c: i for i, c in enumerate(sc)}
        price = None
        if sr and "PREVPRICE" in si and len(sr[0]) > si["PREVPRICE"]:
            price = sr[0][si["PREVPRICE"]]
        with _stock_prev_lock:
            _stock_prev_cache[secid] = (now, price)
        return price
    except Exception:
        return None


def isin_to_secid(isin):
    """Конвертирует isin вида 'ED-9.26' в secid вида 'EDU6' (очень грубо, по маппингу месяцев)."""
    # e.g. ED-9.26 → EDU6, SI-9.26 → SiU6, CR-9.26 → CRU6, EU-9.26 → EuH7
    import re
    if not isin:
        return None
    u = str(isin).strip().upper()
    perpetual = {"USDRUBF", "EURRUBF", "CNYRUBF"}
    if u in perpetual:
        return u
    m = re.match(r'^([A-Za-z]+)-(\d+)\.(\d+)$', isin)
    if not m:
        return None
    code, month_s, year_s = m.group(1), int(m.group(2)), int(m.group(3))
    month_map = {3: 'H', 6: 'M', 9: 'U', 12: 'Z'}
    suffix = month_map.get(month_s)
    if not suffix:
        return None
    year2 = year_s % 10
    # UCNY-9.26 → UCU6 (буква месяца уже входит в тикер UCNY → префикс UC)
    if code.upper() == "UCNY":
        return "UC" + suffix + str(year2)
    return code + suffix + str(year2)


def get_lk_futures_positions():
    """Возвращает список фьючерсных позиций из всех ЛК-аккаунтов с текущей ценой из MOEX.
    Каждый элемент: {login, account, isin, qty, finance_result, total_price_futures, go, currentPrice}
    """
    result = []
    with lk_lock:
        accounts_snapshot = dict(lk_state["accounts"])
    for login, st in accounts_snapshot.items():
        data = (st.get("data") or {})
        positions = data.get("positions") or {}
        if isinstance(positions, dict):
            for acct_id, groups in positions.items():
                if not isinstance(groups, dict):
                    continue
                futures = groups.get("futures") or []
                for pos in (futures if isinstance(futures, list) else []):
                    isin = pos.get("isin") or ""
                    qty = pos.get("position", 0) or 0
                    if qty == 0:
                        continue
                    # Try to get current price via per-secid ISS query
                    secid = isin_to_secid(isin)
                    # Предпочитаем цену из того же снапшота, что и finance_result,
                    # чтобы current и pnl были из одной точки времени.
                    snap_price = pos.get("snapshot_price")
                    cur_price = snap_price if snap_price not in (None, "") else (get_cached_forts_price(secid) if secid else None)
                    result.append({
                        "login": login,
                        "account": acct_id,
                        "isin": isin,
                        "secid": secid,
                        "qty": qty,
                        "finance_result": pos.get("finance_result"),
                        "total_price_futures": pos.get("total_price_futures"),
                        "go": pos.get("go"),
                        "currentPrice": cur_price,
                    })
    return result


def deal_types_with_current():
    """DEAL_TYPES + autoCurrent в каждой ноге (для живого расчёта P&L в форме)."""
    types = []
    for t in DEAL_TYPES:
        t2 = dict(t)
        legs = []
        for ld in t.get("legs") or []:
            ld2 = dict(ld)
            cur = deal_leg_current(ld2)
            if cur is not None:
                ld2["autoCurrent"] = cur
            legs.append(ld2)
        t2["legs"] = legs
        types.append(t2)
    return types


def build_deals_payload():
    deals = enrich_deals(load_deals())
    need_save = any(d.get("allClosed") and d.get("status") == "Закрыта" for d in deals)
    if not need_save:
        raw = load_deals()
        for d, r in zip(deals, raw):
            if d.get("entryPoint") != r.get("entryPoint") or d.get("exitPoint") != r.get("exitPoint"):
                need_save = True
                break
    if need_save:
        save_deals(deals)
    return {
        "types": deal_types_with_current(),
        "deals": deals,
        "goldContracts": gold_contracts_cache["data"] or [],
        "usd": get_usd_rate_cached(),
        "stats": deal_stats(deals),
        "lkPositions": get_lk_futures_positions(),
    }


def build_deals_payload_safe():
    """build_deals_payload с защитой от ошибок: при сбое внешних запросов
    возвращает то, что есть в кеше, чтобы /api/deals не падал."""
    try:
        return build_deals_payload()
    except Exception:
        try:
            deals = enrich_deals(load_deals())
            return {
                "types": deal_types_with_current(),
                "deals": deals,
                "goldContracts": gold_contracts_cache["data"] or [],
                "usd": get_usd_rate_cached(),
                "stats": deal_stats(deals),
                "lkPositions": get_lk_futures_positions(),
            }
        except Exception:
            try:
                deals = load_deals()
                return {
                    "types": DEAL_TYPES,
                    "deals": deals,
                    "goldContracts": gold_contracts_cache["data"] or [],
                    "usd": get_usd_rate_cached(),
                    "stats": deal_stats(deals),
                    "lkPositions": [],
                }
            except Exception:
                return {
                    "types": DEAL_TYPES,
                    "deals": [],
                    "goldContracts": gold_contracts_cache["data"] or [],
                    "usd": get_usd_rate_cached(),
                    "stats": {},
                    "lkPositions": [],
                }


def load_lk_config():
    cfg_path = os.path.join(BASE_DIR, "config.json")
    if not os.path.exists(cfg_path):
        return []
    try:
        with open(cfg_path, encoding="utf-8") as f:
            cfg = json.load(f)
    except Exception:
        return []
    entries = (cfg or {}).get("lite_invest") or []
    if isinstance(entries, dict):
        entries = [entries]
    if not isinstance(entries, list):
        return []
    accounts = []
    for item in entries:
        if not isinstance(item, dict):
            continue
        login = (item.get("login") or "").strip()
        password = item.get("password") or ""
        if login and password:
            accounts.append({"login": login, "password": password})
    return accounts


def fetch_json(url, timeout=15, attempts=3):
    last_err = None
    for attempt in range(attempts):
        try:
            r = subprocess.run(
                ["curl", "-s", "--max-time", str(timeout), url],
                capture_output=True, timeout=timeout + 5,
            )
            if r.returncode != 0:
                last_err = RuntimeError(f"curl error {r.returncode}: {r.stderr.decode()[:200]}")
            else:
                return json.loads(r.stdout)
        except (subprocess.TimeoutExpired, json.JSONDecodeError) as e:
            last_err = e
        if attempt < attempts - 1:
            time.sleep(1.5 * (attempt + 1))
    raise last_err


def load_funding(instr):
    url = (
        f"{ISS_BASE}/engines/futures/markets/swaprates/securities/"
        f"{instr['secid']}.json?iss.meta=off&iss.only=marketdata"
    )
    md = fetch_json(url).get("marketdata", {})
    cols = md.get("columns", [])
    rows = md.get("data", [])
    if not rows:
        return None
    row = dict(zip(cols, rows[0]))
    mult = instr["mult"]
    last = row.get("LAST")
    return {
        "secid": instr["secid"],
        "title": instr["title"],
        "group": instr["group"],
        "url": instr["url"],
        "contract_url": f"https://www.moex.com/ru/contract.aspx?code={instr['secid']}",
        "tradedate": row.get("TRADEDATE"),
        "tradetime": row.get("TRADETIME"),
        "last": last * mult if isinstance(last, (int, float)) else last,
        "yesterday": None,
        "delta": None,
    }


def load_yesterday(instr):
    today = datetime.now(timezone.utc).date()
    from_date = (today - timedelta(days=10)).isoformat()
    url = (
        f"{ISS_BASE}/engines/futures/markets/swaprates/securities/"
        f"{instr['secid']}/candles.json?iss.meta=off&iss.only=candles"
        f"&interval=60&from={from_date}&till={today}"
    )
    candles = fetch_json(url).get("candles", {})
    cols = candles.get("columns", [])
    by_day = {}
    for r in candles.get("data", []):
        m = dict(zip(cols, r))
        day = (m.get("begin") or "")[:10]
        close = m.get("close")
        if not day or day == str(today):
            continue
        if close not in (None, 0):
            by_day[day] = close
    if not by_day:
        return None
    return by_day[max(by_day)]


def _load_instrument(instr):
    """Загрузка одного инструмента фандинга (котировка + вчерашний close)."""
    r = load_funding(instr)
    if r is None:
        return None
    try:
        r["yesterday"] = load_yesterday(instr)
    except Exception:
        r["yesterday"] = None
    if r["yesterday"] is not None:
        r["yesterday"] *= instr["mult"]
    if r["yesterday"] is not None and r["last"] is not None:
        r["delta"] = round(r["last"] - r["yesterday"], 8)
    else:
        r["delta"] = None
    return r


def refresh_once():
    results = []
    errors = []
    with ThreadPoolExecutor(max_workers=min(6, len(INSTRUMENTS) or 1)) as ex:
        futs = {ex.submit(_load_instrument, instr): instr for instr in INSTRUMENTS}
        for fut in as_completed(futs):
            instr = futs[fut]
            try:
                r = fut.result()
                if r is not None:
                    results.append(r)
            except Exception as e:
                errors.append(f"{instr['secid']}: {e}")
    with lock:
        # при полном сбое сохраняем прошлые данные, чтобы таблица не пустела,
        # и НЕ трогаем updated/ts — так данные помечаются устаревшими по времени
        if results:
            state["data"] = results
            state["updated"] = now_msk()
            state["ts"] = time.time()
            state["error"] = None  # при частичном успехе ошибки не показываем
        elif state["data"] is None:
            state["data"] = []
            state["updated"] = now_msk()
            state["ts"] = time.time()
        state["error"] = "; ".join(errors) if not results else None
    _write_json(FUND_CACHE_FILE, {"data": state["data"], "updated": state["updated"], "error": state["error"]})
    return len(errors)


def funding_stale():
    # вызывается уже под lock — не захватываем повторно
    if state["updated"] is None:
        return True
    return time.time() - state["ts"] > FUND_STALE_TTL


def background():
    global _fund_backoff
    last_fund = 0.0
    while True:
        with fund_fetch_lock:
            # Сводка по фандингам: раз в минуту, при ошибках интервал растёт
            if time.time() - last_fund >= _fund_backoff:
                errs = refresh_once()
                last_fund = time.time()
                # частичный сбой (меньше половины инструментов) не критичен —
                # обновляемся как обычно; бэкофф растёт только при масштабном сбое
                if errs * 2 > len(INSTRUMENTS):
                    _fund_backoff = min(_fund_backoff * 2, FUND_TTL_MAX)
                else:
                    _fund_backoff = FUND_TTL
            # Pre-warm caches so /api/deals responds fast
            try:
                load_gold_contracts()
            except Exception:
                pass
            try:
                load_moex_prices()
            except Exception:
                pass
        time.sleep(TTL)


def refresh_now():
    # не блокируем HTTP-поток на время сети: если fund_fetch_lock занят фоновым потоком,
    # пропускаем принудительное обновление и возвращаем текущее состояние кеша
    if fund_fetch_lock.acquire(blocking=False):
        try:
            refresh_once()
        finally:
            fund_fetch_lock.release()
    with lock:
        return {
            "data": state["data"] or [],
            "updated": state["updated"],
            "error": state["error"],
            "usd": get_usd_rate(),
            "stale": funding_stale(),
        }


def _lk_request(req, timeout):
    """Выполняет urlopen с ретраями на таймаут/сетевые ошибки (API ЛК нестабильно)."""
    last_exc = None
    for attempt in range(3):
        try:
            with urllib.request.urlopen(req, timeout=timeout, context=_SSL_CTX) as resp:
                return json.load(resp)
        except Exception as e:
            last_exc = e
            time.sleep(0.5 * (attempt + 1))
    raise last_exc


def _lk_post(path, payload, token=None, timeout=20):
    headers = {"Content-Type": "application/json", "User-Agent": "moex-web/1.0"}
    if token:
        headers["Authorization"] = f"Bearer {token}"
    req = urllib.request.Request(
        LK_API_BASE + path,
        data=json.dumps(payload).encode("utf-8"),
        headers=headers,
        method="POST",
    )
    return _lk_request(req, timeout)


def _lk_get(path, token, params=None, timeout=20):
    url = LK_API_BASE + path
    if params:
        p = urllib.parse.urlencode(params)
        url += "?" + p
    req = urllib.request.Request(
        url, headers={"Authorization": f"Bearer {token}", "User-Agent": "moex-web/1.0"}
    )
    return _lk_request(req, timeout)


def lk_login(cfg):
    resp = _lk_post(LK_LOGIN_PATH, {"identifier": cfg["login"], "password": cfg["password"]})
    token = resp.get("jwt")
    if not token:
        raise RuntimeError("нет JWT в ответе /auth/local")
    return token


def lk_fetch_account(cfg):
    token = lk_login(cfg)

    try:
        balance = _lk_get(LK_BALANCE_PATH, token)
    except Exception as e:
        raise RuntimeError(f"баланс: {e}") from e

    try:
        user = _lk_get(LK_USERS_ME, token, params=None)
    except Exception as e:
        raise RuntimeError(f"пользователь: {e}") from e

    trading_accounts = None
    if isinstance(user, dict):
        ta = user.get("tradingAccounts")
        if isinstance(ta, list):
            trading_accounts = [a.get("number") for a in ta if isinstance(a, dict) and a.get("number")]

    positions = None
    max_losses = None

    def num(v):
        if v in (None, ""):
            return None
        try:
            return float(str(v).replace(",", "."))
        except ValueError:
            return None

    if trading_accounts:
        positions = {}
        funding = snapshot_funding()
        for acc in trading_accounts:
            # 3: фин-рез одного счёта не должен валить весь ЛК — пропускаем счёт при сбое
            try:
                fr = _lk_get(LK_FIN_RESULT, token, params={"account": acc})
            except Exception as e:
                print(f"[lk] фин-рез не получен, счёт {acc} ({cfg['login']}): {e}", flush=True)
                continue
            if not isinstance(fr, dict):
                continue
            acc_pos = {}
            for grp in ("actions", "futures", "currency"):
                items = fr.get(grp)
                if isinstance(items, list):
                    acc_pos[grp] = [
                        {
                            "isin": it.get("isin"),
                            "update_time": it.get("update_time"),
                            "position": it.get("position"),
                            "cms": it.get("cms"),
                            "finance_result": it.get("finance_result"),
                            "max_loss": it.get("max_loss"),
                            "max_loss_alg_type": it.get("max_loss_alg_type"),
                            "assets_coeff": it.get("assets_coeff"),
                            "go": it.get("go"),
                            "in_lot": it.get("in_lot"),
                            "total_price": it.get("total_price"),
                            "total_price_futures": it.get("total_price_futures"),
                            "prev_price": (get_stock_prev_close(it.get("isin")) if grp == "actions" else None),
                            "funding_secid": None,
                            "funding_last": None,
                            "funding_yesterday": None,
                            "snapshot_price": None,
                        }
                        for it in items
                        if isinstance(it, dict)
                    ]
            if acc_pos.get("futures"):
                for it in acc_pos["futures"]:
                    secid = funding_secid_for(it.get("isin"))
                    if not secid:
                        continue
                    frd = funding.get(secid)
                    if not frd:
                        continue
                    pos = num(it.get("position"))
                    if pos is None:
                        continue
                    pos_abs = abs(pos)
                    last = frd.get("last")
                    yest = frd.get("yesterday")
                    it["funding_secid"] = secid
                    it["funding_last"] = round(last * pos_abs, 2) if isinstance(last, (int, float)) else None
                    it["funding_yesterday"] = round(yest * pos_abs, 2) if isinstance(yest, (int, float)) else None
            if acc_pos.get("futures"):
                for it in acc_pos["futures"]:
                    # Цена фиксируется в тот же момент, что и finance_result от ЛК
                    # (один снапшот), чтобы current и pnl были из одной точки времени.
                    secid = isin_to_secid(it.get("isin"))
                    it["snapshot_price"] = get_forts_price(secid, force=True) if secid else None
            max_loss = fr.get("maxLoss")
            if isinstance(max_loss, dict):
                acc_pos["_maxLoss"] = {}
                for grp in ("actions", "futures", "currency"):
                    m = max_loss.get(grp)
                    if isinstance(m, dict):
                        acc_pos["_maxLoss"][grp] = {
                            "max_loss": m.get("max_loss"),
                            "max_loss_alg_type": m.get("max_loss_alg_type"),
                        }
            positions[acc] = acc_pos

        # 3: просадки (max-loss) не фатальны — при сбое вернём их пустыми, остальное сохраняем
        try:
            ml = _lk_get(LK_MAX_LOSS, token)
        except Exception as e:
            print(f"[lk] просадки не получены ({cfg['login']}): {e}", flush=True)
            ml = None
        if isinstance(ml, dict) and isinstance(ml.get("maxLosses"), list):
            max_losses = []
            for mc in ml["maxLosses"]:
                if not isinstance(mc, dict):
                    continue
                ex = mc.get("exchanges")
                row = {"tradingAccount": mc.get("tradingAccount"), "exchanges": {}}
                if isinstance(ex, dict):
                    for grp, rec in ex.items():
                        if not isinstance(rec, dict):
                            continue
                        row["exchanges"][grp] = {
                            "fsr": rec.get("fsr"),
                            "lk": rec.get("lk"),
                        }
                max_losses.append(row)

    real_balance = num(balance.get("realBalance")) if isinstance(balance, dict) else None
    base_balance = num(balance.get("balance")) if isinstance(balance, dict) else None
    under = num(user.get("moexUnderManagementBalance")) if isinstance(user, dict) else None

    payout = payout_rate(base_balance)
    if payout is not None and isinstance(positions, dict) and payout != 1.0:
        for acc_pos in positions.values():
            if not isinstance(acc_pos, dict):
                continue
            for it in acc_pos.get("futures") or []:
                if not isinstance(it, dict):
                    continue
                if it.get("funding_last") is not None:
                    it["funding_last"] = round(it["funding_last"] * (1 - payout), 2)
                if it.get("funding_yesterday") is not None:
                    it["funding_yesterday"] = round(it["funding_yesterday"] * (1 - payout), 2)

    lk_record_balance(cfg["login"], base_balance)
    prev_balance = lk_yesterday_balance(cfg["login"])
    balance_diff = round(base_balance - prev_balance, 2) if prev_balance is not None else None

    available = None
    if base_balance is not None:
        managed = max(0.0, under) if under is not None else 0.0
        available = max(0.0, base_balance - managed)

    total_position = None
    if isinstance(positions, dict):
        s = 0.0
        found = False
        for acc_pos in positions.values():
            if not isinstance(acc_pos, dict):
                continue
            for grp, items in acc_pos.items():
                if grp == "_maxLoss" or not isinstance(items, list):
                    continue
                for it in items:
                    if not isinstance(it, dict):
                        continue
                    if grp == "futures":
                        # Размер позиции = стоимость фьючерсов по цене биржи
                        v = num(it.get("total_price_futures"))
                    elif grp == "actions":
                        # Размер позиции = стоимость акций по цене биржи
                        v = num(it.get("total_price"))
                    else:
                        v = num(it.get("total_price"))
                    if v is not None:
                        s += v
                        found = True
        if found:
            total_position = s

    leverage = None
    if total_position is not None and base_balance:
        leverage = total_position / base_balance

    return {
        "login": cfg["login"],
        "nickname": (user.get("nickname") or user.get("fullname") or user.get("username") or cfg["login"]) if isinstance(user, dict) else cfg["login"],
        "realBalance": real_balance,
        "balance": base_balance,
        "balanceDiff": balance_diff,
        "totalPosition": total_position,
        "leverage": round(leverage, 2) if leverage is not None else None,
        "payout": payout,
        "accounts": trading_accounts,
        "positions": positions,
        "maxLosses": max_losses,
    }


def lk_refresh_once():
    configured = load_lk_config()
    current = {}
    for cfg in configured:
        login = cfg["login"]
        try:
            current[login] = {
                "data": lk_fetch_account(cfg),
                "updated": now_msk(),
                "ts": time.time(),
                "error": None,
            }
        except Exception as e:
            # 502/сбой ЛК: оставляем прошлые данные, чтобы не терять информацию
            prev = lk_state["accounts"].get(login) if lk_state else None
            current[login] = {
                "data": (prev or {}).get("data") if prev else None,
                "updated": (prev or {}).get("updated") if prev else None,
                "ts": (prev or {}).get("ts") if prev else 0.0,
                "error": ct_friendly_error(e),
            }
    with lk_lock:
        lk_state["accounts"] = current


def lk_refresh_now():
    lk_refresh_once()
    with lk_lock:
        return [
            {"login": login, "data": st["data"], "updated": st["updated"], "error": st["error"]}
            for login, st in lk_state["accounts"].items()
        ]


def lk_background():
    while True:
        try:
            with lk_fetch_lock:
                lk_refresh_once()
        except Exception:
            pass
        time.sleep(LK_TTL)


# ---------------------------------------------------------------------------
# Телеграм-бот: предупреждения о просадках ЛК (финрез ≥60% просадки,
# резкое изменение отрицательного финреза ≥20% за час при финрезе ≥60% просадки;
# только в рабочее время МСК — будни 07:00–23:50)
# ---------------------------------------------------------------------------

TG_API = "https://api.telegram.org/bot"


def load_tg_config():
    cfg_path = os.path.join(BASE_DIR, "config.json")
    if not os.path.exists(cfg_path):
        return None
    try:
        with open(cfg_path, encoding="utf-8") as f:
            cfg = json.load(f)
    except Exception:
        return None
    t = (cfg or {}).get("telegram") or {}
    if not isinstance(t, dict):
        return None
    token = (t.get("token") or "").strip()
    chat_id = t.get("chat_id")
    if not token:
        return None
    return {"token": token, "chat_id": str(chat_id) if chat_id is not None else None}


def _tg_send(cfg, text):
    if not cfg or not cfg.get("token") or not cfg.get("chat_id"):
        return
    url = TG_API + cfg["token"] + "/sendMessage"
    req = urllib.request.Request(
        url,
        data=json.dumps({"chat_id": cfg["chat_id"], "text": text, "parse_mode": "HTML"}).encode("utf-8"),
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    for attempt in range(3):
        try:
            with urllib.request.urlopen(req, timeout=20, context=_SSL_CTX) as resp:
                return json.load(resp)
        except Exception:
            time.sleep(0.5 * (attempt + 1))


def _tg_num(v):
    try:
        f = float(str(v).replace(",", "."))
        return f
    except (TypeError, ValueError):
        return None


def _tg_fmt(v):
    if v is None:
        return "—"
    return f"{v:+,.0f}"


TG_DRAWDOWN_PCT = 0.60   # тревога при финрезе ≥60% от просадки
TG_CHANGE_PCT = 0.20     # тревога при росте отрицательного финреза ≥20% за час
TG_CHANGE_WINDOW = 3600  # окно «за час» в секундах

# Не отслеживать: выходные + ночной период (МСК)
TG_NIGHT_START = (23, 50)  # с 23:50
TG_NIGHT_END = (7, 0)      # до 07:00
TG_TZ = ZoneInfo("Europe/Moscow")

tg_armed = {}        # (login, account, grp) -> True (двери взведены)
tg_history = {}      # (login, account, grp) -> [(ts, finrez_sum), ...]
tg_last_notify = {}  # (login, account, grp) -> ts последнего уведомления


def _tg_in_worktime(now_ts):
    """True, если сейчас торговое время (МСК): будний день, 07:00–23:50."""
    dt = datetime.fromtimestamp(now_ts, TG_TZ)
    if dt.weekday() >= 5:  # сб/вс
        return False
    hm = (dt.hour, dt.minute)
    if hm >= TG_NIGHT_START or hm < TG_NIGHT_END:
        return False
    return True


def _tg_lk_snapshot():
    """Сводка финрез/просадка по всем аккаунтам ЛК из свежего кеша."""
    with lk_lock:
        accounts_snapshot = dict(lk_state["accounts"])
    rows = []
    for login, st in accounts_snapshot.items():
        data = (st.get("data") or {})
        positions = data.get("positions") or {}
        if not isinstance(positions, dict):
            continue
        for acct_id, acc_pos in positions.items():
            if not isinstance(acc_pos, dict):
                continue
            ml = acc_pos.get("_maxLoss") or {}
            for grp in ("actions", "futures", "currency"):
                items = acc_pos.get(grp)
                if not isinstance(items, list):
                    continue
                fin = 0.0
                for it in items:
                    if not isinstance(it, dict):
                        continue
                    v = _tg_num(it.get("finance_result"))
                    if v is not None:
                        fin += v
                m = ml.get(grp) or {}
                max_loss = _tg_num(m.get("max_loss"))
                rows.append({
                    "login": login,
                    "account": acct_id,
                    "grp": grp,
                    "fin": round(fin, 2),
                    "max_loss": max_loss,
                })
    return rows


def _tg_check_once(cfg):
    now = time.time()
    if not _tg_in_worktime(now):
        return
    for row in _tg_lk_snapshot():
        key = (row["login"], row["account"], row["grp"])
        fin = row["fin"]
        max_loss = row["max_loss"]
        hist = tg_history.setdefault(key, [])
        hist.append((now, fin))
        hist = [h for h in hist if now - h[0] <= TG_CHANGE_WINDOW + 120]
        tg_history[key] = hist

        # 1) Финрез достиг 60% от просадки (max_loss отрицательный)
        if max_loss is not None and max_loss < 0 and fin <= TG_DRAWDOWN_PCT * max_loss:
            if tg_armed.get(key, True):
                # разница финреза к просадке для сообщения
                pct = (fin / max_loss) * 100 if max_loss else 0
                name = f"{row['login']} · счёт {row['account']} · {GRP_TITLE_GRP[row['grp']]}"
                _tg_send(cfg, f"🚨 <b>Просадка близко</b>\n{name}\nФинрез: {_tg_fmt(fin)} ₽\n"
                              f"Просадка: {_tg_fmt(max_loss)} ₽\nИспользовано: {pct:.0f}% (порог {TG_DRAWDOWN_PCT*100:.0f}%)")
                tg_armed[key] = False
                tg_last_notify[key] = now
        else:
            tg_armed[key] = True

        # 2) Резкое изменение финреза (стал заметно более отрицательным),
        #    но только если финрез уже ≥60% от текущей максимальной просадки
        if len(hist) >= 2:
            prev = next((v for t, v in hist if now - t >= TG_CHANGE_WINDOW * 0.9), None)
            if prev is None:
                prev = hist[0][1]
            if (max_loss is not None and max_loss < 0 and fin <= TG_DRAWDOWN_PCT * max_loss
                    and prev is not None and prev < 0 and fin < prev):
                # насколько выросла просадка относительно базового уровня
                base = abs(prev)
                if base > 1:
                    rel = (prev - fin) / base
                    if rel >= TG_CHANGE_PCT:
                        last = tg_last_notify.get(key, 0)
                        if now - last > TG_CHANGE_WINDOW * 0.5:
                            name = f"{row['login']} · счёт {row['account']} · {GRP_TITLE_GRP[row['grp']]}"
                            _tg_send(cfg, f"⚡ <b>Резкое изменение финреза</b>\n{name}\n"
                                           f"▼ {rel*100:.0f}% за час: {_tg_fmt(prev)} → {_tg_fmt(fin)} ₽")
                            tg_last_notify[key] = now


GRP_TITLE_GRP = {"actions": "Акции", "futures": "Фьючерсы", "currency": "Валюта"}


def tg_background():
    reported_no_token = False
    while True:
        cfg = load_tg_config()
        if not cfg:
            if not reported_no_token:
                print("[tg] телеграм не настроен: в config.json укажите telegram.token и telegram.chat_id", flush=True)
                reported_no_token = True
            time.sleep(60)
            continue
        reported_no_token = False
        try:
            _tg_check_once(cfg)
        except Exception as e:
            print(f"[tg] ошибка проверки: {e}", flush=True)
        time.sleep(30)


# ---------------------------------------------------------------------------
# TradersDiaries (непубличный API) — логин по magic-link токену, ключи, сделки
# ---------------------------------------------------------------------------

def load_td_config():
    cfg_path = os.path.join(BASE_DIR, "config.json")
    if not os.path.exists(cfg_path):
        return None
    try:
        with open(cfg_path, encoding="utf-8") as f:
            cfg = json.load(f)
    except Exception:
        return None
    t = (cfg or {}).get("tradersdiaries") or {}
    if not isinstance(t, dict):
        return None
    token = (t.get("token") or "").strip()
    if not token:
        return None
    return {"token": token, "device_id": (t.get("device_id") or "").strip()}


def _td_request(opener, url, payload=None, headers=None, timeout=25):
    """GET/POST к TD API через opener с куками (sso_session)."""
    data = None
    hdrs = {"User-Agent": "Mozilla/5.0 moex-web"}
    if headers:
        hdrs.update(headers)
    if payload is not None:
        data = json.dumps(payload).encode("utf-8")
        hdrs["Content-Type"] = "application/json"
    req = urllib.request.Request(url, data=data, headers=hdrs, method=("POST" if payload is not None else "GET"))
    last = None
    for attempt in range(3):
        try:
            resp = opener.open(req, timeout=timeout)
            return json.load(resp)
        except Exception as e:
            last = e
            time.sleep(0.5 * (attempt + 1))
    raise last


def td_cookie_jar():
    """Возвращает cookie jar, загруженный с диска (если есть)."""
    jar = http.cookiejar.MozillaCookieJar(TD_COOKIE_PATH)
    try:
        if os.path.exists(TD_COOKIE_PATH):
            jar.load(ignore_discard=True, ignore_expires=True)
    except Exception:
        pass
    return jar


def td_save_cookies(jar):
    try:
        jar.save(ignore_discard=True, ignore_expires=True)
    except Exception:
        pass


def td_try_silent(device_id):
    """Пытается получить accessToken по сохранённой SSO-куке (без magic-link)."""
    jar = td_cookie_jar()
    opener = urllib.request.build_opener(urllib.request.HTTPCookieProcessor(jar))
    try:
        silent = _td_request(opener, TD_ID_API + f"/client/{TD_CLIENT_ID}/oauth/v2/silent?" + urllib.parse.urlencode({"device_id": device_id}))
    except Exception:
        return None
    if not isinstance(silent, dict) or not silent.get("accessToken"):
        return None
    td_save_cookies(jar)
    return silent["accessToken"]


def td_obtain_access_token(cfg):
    """Обменивает magic-link токен на accessToken (JWT). Возвращает (token, device_id)."""
    device_id = cfg.get("device_id") or str(uuid.uuid4())
    jar = td_cookie_jar()
    opener = urllib.request.build_opener(urllib.request.HTTPCookieProcessor(jar))
    params = {
        "client_id": TD_CLIENT_ID,
        "redirect_uri": TD_REDIRECT_URI,
        "from_uri": TD_REDIRECT_URI,
        "device_id": device_id,
        "lang": "en",
        "token": cfg["token"],
    }
    r = _td_request(opener, TD_ID_API + "/ui/public/magic-link/login?" + urllib.parse.urlencode(params))
    if not isinstance(r, dict) or not r.get("redirectUri"):
        raise RuntimeError(f"TD magic-link login: неожиданный ответ {str(r)[:200]!r}")
    silent = _td_request(opener, TD_ID_API + f"/client/{TD_CLIENT_ID}/oauth/v2/silent?" + urllib.parse.urlencode({"device_id": device_id}))
    if not isinstance(silent, dict) or not silent.get("accessToken"):
        raise RuntimeError(f"TD silent auth: неожиданный ответ {str(silent)[:200]!r}")
    td_save_cookies(jar)
    return silent["accessToken"], device_id


def _td_req(url, payload=None):
    """Выполняет запрос к TD API с автообновлением accessToken при 401."""
    global td_token, _td_opener_
    for attempt in range(2):
        with td_lock:
            token = td_token.get("access")
        if not token or time.time() >= td_token.get("exp", 0.0) - 60:
            cfg = load_td_config()
            if not cfg:
                raise RuntimeError("TD: не настроено (нет tradersdiaries в config.json)")
            device_id = td_token.get("device_id") or cfg.get("device_id")
            refreshed = None
            if device_id:
                refreshed = td_try_silent(device_id)
            if not refreshed:
                token, device_id = td_obtain_access_token(cfg)
            else:
                token = refreshed
            with td_lock:
                td_token["access"] = token
                td_token["device_id"] = device_id
                try:
                    b = token.split(".")[1].encode() + b"=" * 3
                    td_token["exp"] = json.loads(base64.urlsafe_b64decode(b).decode("utf-8")).get("exp", time.time() + 590)
                except Exception:
                    td_token["exp"] = time.time() + 590
        try:
            r = _td_request(_td_opener_, url, payload, {"X-Authorization": token})
            return r
        except urllib.error.HTTPError as e:
            if e.code == 401:
                with td_lock:
                    td_token["access"] = None
                continue
            raise
        except Exception as e:
            if "401" in str(e) and "HTTP" in str(e):
                with td_lock:
                    td_token["access"] = None
                continue
            raise
    raise RuntimeError("TD: повторный 401 после обновления токена")


def td_lk_finrez_lookup():
    """Строит карту (счёт, isin) -> finance_result из lk_state.

    Ключ: f"{acc_num}|{isin.upper()}". Данные ЛК обновляются отдельным
    потоком (lk_background), поэтому могут быть слегка устаревшими.
    """
    lookup = {}
    with lk_lock:
        snapshot = dict(lk_state.get("accounts") or {})
    for st in snapshot.values():
        data = st.get("data") or {}
        positions = data.get("positions") or {}
        if not isinstance(positions, dict):
            continue
        for acc_num, acc_pos in positions.items():
            if not isinstance(acc_pos, dict):
                continue
            for grp, items in acc_pos.items():
                if grp == "_maxLoss" or not isinstance(items, list):
                    continue
                for it in items:
                    if not isinstance(it, dict):
                        continue
                    isin = it.get("isin")
                    if not isin:
                        continue
                    lookup[f"{acc_num}|{str(isin).upper()}"] = it.get("finance_result")
    return lookup


def td_avg_entry_price(position):
    """Средняя цена входа по позиции (по всем сделкам позиции).

    avg = Σ(price×amount) / Σ(amount) по ВСЕМ сделкам диапазона
    (deal1_id..deal2_id). Частичные закрытия учитываются знаком amount
    (sell — отрицательный), что даёт среднюю цену по оставшейся позиции.
    Возвращает None при отсутствии данных.
    """
    try:
        deals = _td_req(TD_API_BASE + "/prop/get-position-deals", {
            "trader_guid": position.get("trader_guid"),
            "board": position.get("board"),
            "symbol": position.get("symbol"),
            "deal1_id": position.get("deal1_id"),
            "deal2_id": position.get("deal2_id"),
        })
    except Exception:
        deals = []
    if not isinstance(deals, list):
        return None
    tot = 0.0
    amt = 0.0
    for d in deals:
        if not isinstance(d, dict):
            continue
        try:
            price = float(d.get("price") or 0)
            amount = float(d.get("amount") or 0)
        except (TypeError, ValueError):
            continue
        if amount == 0:
            continue
        tot += price * amount
        amt += amount
    if amt == 0:
        return None
    return round(tot / amt, 2)


def td_fetch():
    """Загружает ключи аккаунтов, сделки по каждому ключу и prop-позиции."""
    keys = _td_req(TD_API_BASE + "/lk/key/get-keys")
    if not isinstance(keys, list):
        raise RuntimeError(f"TD keys: неожиданный ответ {str(keys)[:200]!r}")
    accounts = []
    for k in keys:
        key_id = k.get("id")
        try:
            body = {"key_id": key_id, "date_from": "2026-01-01"}
            trades = _td_req(TD_API_BASE + "/crypto/get-trades", body)
            rows = trades.get("rows") or [] if isinstance(trades, dict) else []
        except Exception:
            rows = []
        accounts.append({
            "key_id": key_id,
            "market": k.get("market"),
            "masked_token": k.get("masked_token"),
            "balance": k.get("balance"),
            "valid": k.get("valid"),
            "trades": rows,
        })
    positions = _td_req(TD_API_BASE + "/prop/get-positions", {})
    if not isinstance(positions, list):
        positions = []
    finrez = td_lk_finrez_lookup()
    for p in positions:
        if not isinstance(p, dict):
            continue
        key = f"{p.get('key_name')}|{str(p.get('symbol') or '').upper()}"
        fr = finrez.get(key)
        if fr is not None:
            p["finrez"] = fr
        p["avg_entry"] = td_avg_entry_price(p)
    return {"keys": keys, "accounts": accounts, "positions": positions}


def td_refresh_once():
    configured = load_td_config()
    current = {}
    if configured:
        try:
            data = td_fetch()
            current = {
                "data": data,
                "updated": now_msk(),
                "ts": time.time(),
                "error": None,
            }
        except Exception as e:
            prev = td_state.get("accounts") or {}
            prev_data = prev.get("data") if isinstance(prev, dict) else None
            current = {
                "data": prev_data,
                "updated": prev.get("updated") if isinstance(prev, dict) else None,
                "ts": prev.get("ts", 0.0) if isinstance(prev, dict) else 0.0,
                "error": ct_friendly_error(e),
            }
    with td_lock:
        td_state["accounts"] = current
        td_state["updated"] = current.get("updated")
        td_state["error"] = current.get("error")
        td_state["ts"] = current.get("ts", 0.0)


def td_refresh_now():
    td_refresh_once()
    with td_lock:
        return td_state.get("accounts")


def td_background():
    while True:
        try:
            with td_fetch_lock:
                td_refresh_once()
        except Exception:
            pass
        time.sleep(TD_TTL)


# ---------------------------------------------------------------------------
# cTrader Open API (xpbee / cTrader) — WebSocket JSON, RFC6455 on stdlib
# ---------------------------------------------------------------------------

CT_WS_HOSTS = {"live": ("live.ctraderapi.com", 5036), "demo": ("demo.ctraderapi.com", 5036)}

CT_TOKEN_URL = "https://openapi.ctrader.com/apps/token"
CT_TOKEN_ERRORS = {1, 104, 105}  # OA_AUTH_TOKEN_EXPIRED, CH_ACCESS_TOKEN_INVALID, CH_SERVER_NOT_REACHABLE

CT_PT = {
    "APP_AUTH_REQ": 2100,
    "APP_AUTH_RES": 2101,
    "ACCOUNT_AUTH_REQ": 2102,
    "ACCOUNT_AUTH_RES": 2103,
    "SYMBOLS_LIST_REQ": 2114,
    "SYMBOLS_LIST_RES": 2115,
    "SYMBOL_BY_ID_REQ": 2112,
    "SYMBOL_BY_ID_RES": 2113,
    "TRADER_REQ": 2121,
    "TRADER_RES": 2122,
    "RECONCILE_REQ": 2124,
    "RECONCILE_RES": 2125,
    "ACCOUNTS_BY_TOKEN_REQ": 2149,
    "ACCOUNTS_BY_TOKEN_RES": 2150,
    "ERROR_RES": 2142,
    "UNREALIZED_PNL_REQ": 2187,
    "UNREALIZED_PNL_RES": 2188,
    "HEARTBEAT_EVENT": 51,
}

CT_TTL = 60
ct_state = {"accounts": {}}
ct_lock = threading.Lock()
ct_symbols_cache = {}  # symbolId (int) -> имя символа (кэш, т.к. SYMBOLS_LIST_REQ ненадёжен)

# Запасной маппинг symbolId -> имя символа. cTrader крайне ненадёжно отдаёт
# имена символов (ни SYMBOLS_LIST_REQ, ни SymbolByIdReq не отвечают с этого
# окружения), поэтому без этого маппинга живые позиции несут только числовой
# symbolId и сделки не могут сопоставить форекс-позицию по имени. Значения
# сверены с реальными позициями (совпадение цены входа/стороны/единиц).
CT_FALLBACK_SYMBOLS = {1718: "XAUUSD", 1678: "EURUSD"}
ct_symbols_cache.update(CT_FALLBACK_SYMBOLS)


class CtWebSocket:
    def __init__(self, host, port, timeout=20):
        self.host = host
        self.port = port
        self.timeout = timeout
        self.sock = None
        self.buf = b""

    def connect(self):
        ctx = ssl.create_default_context()
        raw = socket.create_connection((self.host, self.port), timeout=self.timeout)
        self.sock = ctx.wrap_socket(raw, server_hostname=self.host)
        key = base64.b64encode(os.urandom(16)).decode("ascii")
        req = (
            f"GET / HTTP/1.1\r\n"
            f"Host: {self.host}:{self.port}\r\n"
            "Upgrade: websocket\r\n"
            "Connection: Upgrade\r\n"
            f"Sec-WebSocket-Key: {key}\r\n"
            "Sec-WebSocket-Version: 13\r\n\r\n"
        )
        self.sock.sendall(req.encode("ascii"))
        headers = self._read_headers()
        if "101" not in headers.split("\r\n", 1)[0]:
            raise RuntimeError(f"WebSocket upgrade failed: {headers[:200]}")

    def _read_headers(self):
        while b"\r\n\r\n" not in self.buf:
            chunk = self.sock.recv(4096)
            if not chunk:
                raise RuntimeError("соединение закрыто при рукопожатии")
            self.buf += chunk
        idx = self.buf.index(b"\r\n\r\n")
        headers = self.buf[:idx].decode("utf-8", "replace")
        self.buf = self.buf[idx + 4:]
        return headers

    def _recv_exact(self, n):
        while len(self.buf) < n:
            chunk = self.sock.recv(65536)
            if not chunk:
                raise RuntimeError("соединение закрыто")
            self.buf += chunk
        data = self.buf[:n]
        self.buf = self.buf[n:]
        return data

    def send_text(self, text):
        payload = text.encode("utf-8")
        mask = os.urandom(4)
        masked = bytes(b ^ mask[i % 4] for i, b in enumerate(payload))
        n = len(payload)
        if n < 126:
            head = bytes([0x81, 0x80 | n])
        elif n < 65536:
            head = bytes([0x81, 0x80 | 126]) + struct.pack(">H", n)
        else:
            head = bytes([0x81, 0x80 | 127]) + struct.pack(">Q", n)
        self.sock.sendall(head + mask + masked)

    def recv_text(self, timeout=20):
        self.sock.settimeout(timeout)
        opcode = None
        payload = b""
        while True:
            b0, b1 = self._recv_exact(2)
            fin = b0 & 0x80
            op = b0 & 0x0F
            masked = b1 & 0x80
            ln = b1 & 0x7F
            if ln == 126:
                ln = struct.unpack(">H", self._recv_exact(2))[0]
            elif ln == 127:
                ln = struct.unpack(">Q", self._recv_exact(8))[0]
            mask_key = self._recv_exact(4) if masked else None
            data = self._recv_exact(ln)
            if mask_key:
                data = bytes(b ^ mask_key[i % 4] for i, b in enumerate(data))
            if op == 0x9:  # ping
                self._send_frame(0xA, data)
                continue
            if op == 0x8:  # close
                raise RuntimeError("соединение закрыто сервером")
            if opcode is None:
                opcode = op
            payload += data
            if fin:
                break
        if opcode == 0x1:
            return payload.decode("utf-8", "replace")
        raise RuntimeError(f"неожиданный ws фрейм opcode={opcode}")

    def _send_frame(self, opcode, payload):
        if hasattr(payload, "encode"):
            payload = payload.encode("utf-8")
        mask = os.urandom(4)
        masked = bytes(b ^ mask[i % 4] for i, b in enumerate(payload))
        n = len(payload)
        if n < 126:
            head = bytes([0x80 | opcode, 0x80 | n])
        elif n < 65536:
            head = bytes([0x80 | opcode, 0x80 | 126]) + struct.pack(">H", n)
        else:
            head = bytes([0x80 | opcode, 0x80 | 127]) + struct.pack(">Q", n)
        self.sock.sendall(head + mask + masked)

    def close(self):
        try:
            self._send_frame(0x8, b"\x03\xe8")
        except Exception:
            pass
        try:
            self.sock.close()
        except Exception:
            pass


def load_ct_config():
    cfg_path = os.path.join(BASE_DIR, "config.json")
    if not os.path.exists(cfg_path):
        return []
    try:
        with open(cfg_path, encoding="utf-8") as f:
            cfg = json.load(f)
    except Exception:
        return []
    entries = (cfg or {}).get("ctrader") or []
    if isinstance(entries, dict):
        entries = [entries]
    if not isinstance(entries, list):
        return []
    out = []
    for item in entries:
        if not isinstance(item, dict):
            continue
        client_id = (item.get("client_id") or item.get("clientId") or "").strip()
        client_secret = item.get("client_secret") or item.get("clientSecret") or ""
        access_token = item.get("access_token") or item.get("accessToken") or ""
        refresh_token = item.get("refresh_token") or item.get("refreshToken") or ""
        host = (item.get("host") or "live").strip().lower()
        label = (item.get("label") or "").strip() or client_id
        if not (client_id and client_secret):
            continue
        out.append(
            {
                "client_id": client_id,
                "client_secret": client_secret,
                "access_token": access_token,
                "refresh_token": refresh_token,
                "host": host if host in CT_WS_HOSTS else "live",
                "label": label,
            }
        )
    return out


def ct_send(ws, msg_id, payload_type, payload):
    envelope = {
        "clientMsgId": msg_id,
        "payloadType": payload_type,
        "payload": payload,
    }
    ws.send_text(json.dumps(envelope))
    return msg_id


class CtTokenError(RuntimeError):
    pass


def ct_wait(ws, msg_id, want_types, timeout=25):
    deadline = time.time() + timeout
    while time.time() < deadline:
        text = ws.recv_text(max(5, deadline - time.time()))
        msg = json.loads(text)
        pt = msg.get("payloadType")
        if pt == CT_PT["ERROR_RES"]:
            err = (msg.get("payload") or {})
            code = err.get("errorCode") or ""
            desc = err.get("description") or ""
            if isinstance(code, (int, float)) and int(code) in CT_TOKEN_ERRORS:
                raise CtTokenError(f"токен истёк или невалиден ({code}): {desc}")
            raise RuntimeError(f"cTrader error {desc or code}")
        if pt in want_types:
            return msg
        if pt == CT_PT["HEARTBEAT_EVENT"]:
            continue
    raise RuntimeError(f"таймаут ожидания ответа {msg_id}")


def ct_connect(cfg):
    host, port = CT_WS_HOSTS[cfg["host"]]
    ws = CtWebSocket(host, port, timeout=25)
    ws.connect()
    return ws


def ct_save_tokens(cfg, access_token, refresh_token):
    cfg_path = os.path.join(BASE_DIR, "config.json")
    try:
        with open(cfg_path, encoding="utf-8") as f:
            data = json.load(f)
    except Exception:
        return
    entries = (data or {}).get("ctrader") or []
    if isinstance(entries, dict):
        entries = [entries]
    for item in entries:
        if isinstance(item, dict) and (item.get("client_id") or item.get("clientId")) == cfg["client_id"]:
            item["access_token"] = access_token
            item["refresh_token"] = refresh_token
            break
    data["ctrader"] = entries
    try:
        with open(cfg_path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    except Exception:
        pass


def ct_refresh_token(cfg):
    if not cfg.get("refresh_token"):
        raise RuntimeError("нет refresh_token для автообновления токена")
    params = urllib.parse.urlencode(
        {
            "grant_type": "refresh_token",
            "refresh_token": cfg["refresh_token"],
            "client_id": cfg["client_id"],
            "client_secret": cfg["client_secret"],
        }
    )
    req = urllib.request.Request(
        f"{CT_TOKEN_URL}?{params}",
        headers={"Accept": "application/json", "Content-Type": "application/json", "User-Agent": "moex-web/1.0"},
    )
    with urllib.request.urlopen(req, timeout=20, context=_SSL_CTX) as resp:
        data = json.load(resp)
    access_token = data.get("accessToken")
    refresh_token = data.get("refreshToken")
    if not access_token:
        raise RuntimeError(f"не удалось обновить токен: {data}")
    ct_save_tokens(cfg, access_token, refresh_token or cfg["refresh_token"])
    return access_token, refresh_token or cfg["refresh_token"]


def ct_fetch_account(cfg):
    try:
        return ct_fetch_account_once(cfg)
    except CtTokenError:
        if not cfg.get("refresh_token"):
            raise
        at, rt = ct_refresh_token(cfg)
        cfg = dict(cfg)
        cfg["access_token"] = at
        cfg["refresh_token"] = rt
        return ct_fetch_account_once(cfg)
    except OSError:
        # транзитный таймаут/сбой соединения с cTrader — повторяем с новым соединением
        return ct_fetch_account_once(cfg)


def ct_fetch_account_once(cfg):
    ws = ct_connect(cfg)
    try:
        ct_send(ws, "auth", CT_PT["APP_AUTH_REQ"], {"clientId": cfg["client_id"], "clientSecret": cfg["client_secret"]})
        ct_wait(ws, "auth", {CT_PT["APP_AUTH_RES"]})

        ct_send(ws, "accs", CT_PT["ACCOUNTS_BY_TOKEN_REQ"], {"accessToken": cfg["access_token"]})
        acc_res = ct_wait(ws, "accs", {CT_PT["ACCOUNTS_BY_TOKEN_RES"]})
        accounts = [
            a
            for a in (acc_res.get("payload") or {}).get("ctidTraderAccount") or []
            if isinstance(a, dict)
        ]
        if not accounts:
            raise RuntimeError("нет счетов по access token")

        results = []
        for acc in accounts:
            trader_account_id = acc.get("ctidTraderAccountId")
            if trader_account_id is None:
                continue
            try:
                results.append(ct_fetch_one(ws, cfg, trader_account_id))
            except Exception as e:
                results.append(
                    {
                        "login": acc.get("traderLogin") if isinstance(acc.get("traderLogin"), (int, float)) else str(acc.get("traderLogin") or trader_account_id),
                        "traderAccountId": trader_account_id,
                        "error": ct_friendly_error(e),
                    }
                )
        return results
    finally:
        ws.close()


def ct_wait_safe(ws, msg_id, want_types, timeout=10):
    """Как ct_wait, но при таймауте/ошибке возвращает None (не ломает весь расчёт)."""
    try:
        return ct_wait(ws, msg_id, want_types, timeout=timeout)
    except Exception:
        return None


def ct_fetch_one(ws, cfg, trader_account_id):
    ct_send(ws, f"auth-{trader_account_id}", CT_PT["ACCOUNT_AUTH_REQ"],
            {"ctidTraderAccountId": trader_account_id, "accessToken": cfg["access_token"]})
    ct_wait(ws, f"auth-{trader_account_id}", {CT_PT["ACCOUNT_AUTH_RES"]})

    ct_send(ws, f"trader-{trader_account_id}", CT_PT["TRADER_REQ"], {"ctidTraderAccountId": trader_account_id})
    trader_res = ct_wait_safe(ws, f"trader-{trader_account_id}", {CT_PT["TRADER_RES"]})
    trader = (trader_res.get("payload") or {}).get("trader") or {}
    money_digits = trader.get("moneyDigits")
    if money_digits in (None, 0):
        money_digits = 8
    scale = 10.0 ** money_digits if money_digits else 1.0
    login = trader.get("traderLogin") if isinstance(trader.get("traderLogin"), (int, float)) else trader_account_id
    balance = trader.get("balance")
    balance = balance / scale if isinstance(balance, (int, float)) else None
    deposit_asset_id = trader.get("depositAssetId")

    ct_send(ws, f"rec-{trader_account_id}", CT_PT["RECONCILE_REQ"],
            {"ctidTraderAccountId": trader_account_id})
    rec_res = ct_wait_safe(ws, f"rec-{trader_account_id}", {CT_PT["RECONCILE_RES"]})
    positions = [p for p in (rec_res.get("payload") or {}).get("position") or [] if isinstance(p, dict)] if rec_res else []

    # Имена символов берём из кэша: SYMBOLS_LIST_REQ ненадёжен и, главное,
    # "отравляет" соединение — после него cTrader перестаёт отвечать на любые
    # последующие запросы (в т.ч. PnL). Поэтому список символов обновляется
    # отдельным изолированным фоновым запросом (ct_refresh_symbols_once),
    # а здесь, при отсутствии имени, показываем symbolId.
    symbols = dict(ct_symbols_cache)

    if positions:
        ct_send(ws, f"pnl-{trader_account_id}", CT_PT["UNREALIZED_PNL_REQ"],
                {"ctidTraderAccountId": trader_account_id, "positionId": [p.get("positionId") for p in positions]})
        pnl_res = ct_wait_safe(ws, f"pnl-{trader_account_id}", {CT_PT["UNREALIZED_PNL_RES"]})
        pnl_map = {}
        pnl_digits = None
        if pnl_res:
            for p in (pnl_res.get("payload") or {}).get("positionUnrealizedPnL") or []:
                if isinstance(p, dict) and p.get("positionId") is not None:
                    pnl_map[p["positionId"]] = p
                    if p.get("moneyDigits") not in (None, 0):
                        pnl_digits = p["moneyDigits"]
        pnl_scale = 10.0 ** pnl_digits if pnl_digits else scale
    else:
        pnl_map, pnl_scale = {}, scale

    pos_list = []
    for p in positions:
        td = p.get("tradeData") or {}
        pnl = pnl_map.get(p.get("positionId"))
        open_ts_ms = td.get("openTimestamp")
        open_msk = None
        if isinstance(open_ts_ms, (int, float)) and open_ts_ms > 0:
            open_msk = datetime.fromtimestamp(open_ts_ms / 1000.0, MSK).strftime("%Y-%m-%d %H:%M:%S")
        open_date = None
        if open_msk:
            open_date = open_msk[:10]
        usd_at_open = get_usd_rate_at(open_date) if open_date else None
        net_pnl = (pnl.get("netUnrealizedPnL") / pnl_scale) if pnl and isinstance(pnl.get("netUnrealizedPnL"), (int, float)) else None
        gross_pnl = (pnl.get("grossUnrealizedPnL") / pnl_scale) if pnl and isinstance(pnl.get("grossUnrealizedPnL"), (int, float)) else None
        pos_list.append(
            {
                "symbolId": td.get("symbolId"),
                "symbol": symbols.get(td.get("symbolId"), str(td.get("symbolId") if td.get("symbolId") is not None else "")),
                "side": "buy" if td.get("tradeSide") == 0 else "sell",
                "volume": td.get("volume"),
                "volumeUnits": (td.get("volume") / 100.0) if isinstance(td.get("volume"), (int, float)) else None,
                "price": p.get("price"),
                "swap": (p.get("swap") / scale) if isinstance(p.get("swap"), (int, float)) else None,
                "commission": (p.get("commission") / scale) if isinstance(p.get("commission"), (int, float)) else None,
                "grossPnl": gross_pnl,
                "netPnl": net_pnl,
                "openTime": open_msk,
                "usdAtOpen": usd_at_open,
                "pnlRub": (net_pnl * usd_at_open) if net_pnl is not None and usd_at_open else None,
            }
        )

    total_net = sum(p["netPnl"] for p in pos_list if p["netPnl"] is not None)
    total_gross = sum(p["grossPnl"] for p in pos_list if p["grossPnl"] is not None)
    total_swap = sum(p["swap"] for p in pos_list if p["swap"] is not None)

    return {
        "login": str(login),
        "traderAccountId": trader_account_id,
        "depositAssetId": deposit_asset_id,
        "balance": balance,
        "equity": (balance + total_net) if balance is not None else None,
        "positions": pos_list,
        "positionCount": len(pos_list),
        "totalNetPnl": total_net,
        "totalGrossPnl": total_gross,
        "totalSwap": total_swap,
    }


def ct_friendly_error(e):
    """Переводит низкоуровневые сетевые ошибки cTrader в понятное сообщение."""
    msg = str(e)
    low = msg.lower()
    if "timed out" in low or "timeout" in low or isinstance(e, TimeoutError):
        return "нет ответа от cTrader (таймаут соединения)"
    if "connection" in low and ("refused" in low or "reset" in low):
        return "нет соединения с cTrader (connection refused/reset)"
    if "certificate" in low or "ssl" in low:
        return "ошибка TLS при соединении с cTrader"
    return msg


def ct_refresh_symbols_once():
    """Обновляет ct_symbols_cache отдельным изолированным соединением.

    SYMBOLS_LIST_REQ крайне ненадёжен и «отравляет» сокет (после него cTrader
    перестаёт отвечать на другие запросы). Поэтому гоняем его в отдельном
    соединении, чтобы не ломать основной расчёт позиций/PnL.
    """
    for cfg in load_ct_config():
        if not cfg.get("access_token"):
            continue
        try:
            ws = ct_connect(cfg)
            try:
                ct_send(ws, "auth", CT_PT["APP_AUTH_REQ"], {"clientId": cfg["client_id"], "clientSecret": cfg["client_secret"]})
                ct_wait(ws, "auth", {CT_PT["APP_AUTH_RES"]})
                ct_send(ws, "accs", CT_PT["ACCOUNTS_BY_TOKEN_REQ"], {"accessToken": cfg["access_token"]})
                acc_res = ct_wait(ws, "accs", {CT_PT["ACCOUNTS_BY_TOKEN_RES"]})
                accounts = [a for a in (acc_res.get("payload") or {}).get("ctidTraderAccount") or [] if isinstance(a, dict)]
                for acc in accounts:
                    tid = acc.get("ctidTraderAccountId")
                    if tid is None:
                        continue
                    try:
                        ct_send(ws, f"sa-{tid}", CT_PT["ACCOUNT_AUTH_REQ"], {"ctidTraderAccountId": tid, "accessToken": cfg["access_token"]})
                        ct_wait(ws, f"sa-{tid}", {CT_PT["ACCOUNT_AUTH_RES"]})
                        ct_send(ws, f"sym-{tid}", CT_PT["SYMBOLS_LIST_REQ"], {"ctidTraderAccountId": tid})
                        sym_res = ct_wait(ws, f"sym-{tid}", {CT_PT["SYMBOLS_LIST_RES"]}, timeout=15)
                        got = 0
                        for s in (sym_res.get("payload") or {}).get("symbol") or []:
                            if isinstance(s, dict) and s.get("symbolId") is not None and s.get("symbolName"):
                                ct_symbols_cache[s["symbolId"]] = s["symbolName"]
                                got += 1
                        if got:
                            print(f"[ct] обновлено имён символов: {got}")
                    except Exception as e:
                        print(f"[ct] список символов недоступен ({tid}): {e}")
            finally:
                try: ws.close()
                except Exception:
                    pass
        except Exception as e:
            print(f"[ct] не удалось обновить символы: {e}")


def ct_refresh_once():
    configured = load_ct_config()
    current = {}
    for cfg in configured:
        label = cfg["label"]
        if not cfg["access_token"]:
            current[label] = {
                "data": None,
                "updated": None,
                "error": "Не задан access_token в config.json. Получите токен, нажав Playground в openapi.ctrader.com → вставьте access_token и refresh_token в конфиг.",
            }
            continue
        try:
            current[label] = {
                "data": {"label": label, "accounts": ct_fetch_account(cfg)},
                "updated": now_msk(),
                "error": None,
            }
        except Exception as e:
            with ct_lock:
                old = ct_state["accounts"].get(label)
            if old and old.get("data") is not None:
                current[label] = {
                    "data": old["data"],
                    "updated": old.get("updated"),
                    "error": ct_friendly_error(e),
                    "ts": old.get("ts", 0),
                }
            else:
                current[label] = {"data": None, "updated": None, "error": ct_friendly_error(e)}
    with ct_lock:
        ct_state["accounts"] = current
    # сохраняем последние успешные данные, чтобы они переживали перезапуск/таймауты cTrader
    if any(st.get("data") is not None for st in current.values()):
        save_ct_cache()


def ct_current_entries():
    with ct_lock:
        return [
            {"label": label, "data": st["data"], "updated": st["updated"], "error": st["error"]}
            for label, st in ct_state["accounts"].items()
        ]


ct_refresh_running = False


def ct_trigger_refresh():
    """Запускает обновление cTrader в фоне, не блокируя HTTP-запрос."""
    global ct_refresh_running
    if ct_refresh_running:
        return
    if not ct_fetch_lock.acquire(blocking=False):
        # обновление уже идёт (фоновое или ручное) — второй раз не запускаем
        return
    ct_refresh_running = True

    def _run():
        global ct_refresh_running
        try:
            ct_refresh_once()
        finally:
            ct_refresh_running = False
            try:
                ct_fetch_lock.release()
            except Exception:
                pass

    threading.Thread(target=_run, daemon=True).start()


def ct_background():
    backoff = CT_TTL
    last_sym_refresh = 0.0
    while True:
        try:
            with ct_fetch_lock:
                ct_refresh_once()
            # изолированное обновление имён символов раз в ~5 мин (не в критическом пути)
            now = time.time()
            if now - last_sym_refresh > 300:
                try:
                    ct_refresh_symbols_once()
                    save_ct_cache()
                except Exception:
                    pass
                last_sym_refresh = now
            with ct_lock:
                ok = any(st.get("data") is not None for st in ct_state["accounts"].values())
            backoff = CT_TTL if ok else min(backoff * 2, 300)
        except Exception:
            backoff = min(backoff * 2, 300)
        time.sleep(backoff)


PAGE = """<!DOCTYPE html>
<html lang="ru">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<link rel="icon" type="image/png" href="/favicon.png">
<title>Терминал MOEX Forex</title>
<style>
  body { font-family: 'Segoe UI', Roboto, Arial, sans-serif; background:#0e1420; color:#e6edf3; margin:0; padding:18px; }
  h1 { font-size:19px; margin:0; }
  .header { display:grid; grid-template-columns:1fr auto 1fr; align-items:center; gap:10px; margin-bottom:12px; }
  .h-left { justify-self:start; }
  .h-center { text-align:center; white-space:nowrap; }
  .h-right { justify-self:end; }
  .sub { color:#8b949e; font-size:12px; }
  .card { display:grid; grid-template-columns:repeat(auto-fill,minmax(250px,1fr)); gap:10px; }
  .deal-card { display:block; }
  .item { background:#161d2b; border:1px solid #283349; border-radius:8px; padding:10px 12px; }
  .item.clickable { cursor:pointer; text-decoration:none; color:inherit; display:block; transition:border-color .15s, transform .1s; }
  .item.clickable:hover { border-color:#3fb950; transform:translateY(-1px); }
  .item .head { display:flex; justify-content:space-between; align-items:baseline; gap:8px; }
  .item .name { font-weight:600; font-size:13px; color:#e6edf3; text-decoration:none; }
  .item .name:hover { text-decoration:underline; color:#58a6ff; }
  .item .group { color:#8b949e; font-size:11px; text-decoration:none; white-space:nowrap; }
  .item .group:hover { text-decoration:underline; color:#58a6ff; }
  .item .val { font-size:22px; font-weight:700; margin:6px 0 4px; }
  .pos { color:#3fb950; } .neg { color:#f85149; } .flat { color:#8b949e; } .warn { color:#e3b341; }
  .fund-yest { color:#8b949e; font-size:14px; font-weight:600; }
  .err { background:#3a1d1d; border:1px solid #7d3434; color:#ffb4b4; padding:10px; border-radius:8px; margin-bottom:14px; font-size:12px; }
  .stale { opacity:.62; font-style:italic; }
  .stale .val { opacity:.85; }
  .stale-badge { display:inline-block; color:#e3b341; font-size:11px; font-weight:700; font-style:normal; margin-left:8px; opacity:1 !important; }
  .tabs { display:flex; gap:8px; margin-bottom:16px; }
  .tab { background:#161d2b; border:1px solid #283349; color:#8b949e; border-radius:8px; padding:8px 16px; font-size:14px; cursor:pointer; }
  .tab:hover { color:#e6edf3; }
  .tab.active { background:#1f6feb; border-color:#1f6feb; color:#fff; }
  .tabpane { display:none; }
  .tabpane.active { display:block; }
  .lk { background:#131a28; border:1px solid #2c3a55; border-radius:8px; padding:12px 14px; margin-bottom:14px; }
  .lk h2 { font-size:14px; margin:0 0 10px; color:#b8c7e0; }
  .lk h2.lk-head { display:flex; align-items:center; justify-content:space-between; gap:10px; }
  .lk .fold { background:transparent; border:1px solid #2c3a55; color:#8b949e; border-radius:4px; cursor:pointer; font-size:11px; padding:2px 8px; }
  .lk .fold:hover { color:#b8c7e0; border-color:#4a5f85; }
  .lk.collapsed .fold::after { content:' ▸'; }
  .lk:not(.collapsed) .fold::after { content:' ▾'; }
  .lk.collapsed .ops, .lk.collapsed .stats { display:none; }
  .lk h2 .pay { font-size:12px; color:#8b949e; font-weight:600; white-space:nowrap; }
  .lk .stat .sub.lev { font-size:12px; }
  .lk .stat .sub.lev b { font-size:13px; font-weight:700; }
  .lk h3 { font-size:13px; margin:14px 0 6px; color:#9fb2cf; }
  .lk .stats { display:grid; grid-template-columns:repeat(auto-fit,minmax(140px,1fr)); gap:10px; }
  .lk .stat { background:#0e1525; border:1px solid #24314a; border-radius:6px; padding:8px 10px; }
  .lk .stat .k { font-size:11px; color:#8b949e; }
  .lk .stat .v { font-size:16px; font-weight:700; margin-top:2px; }
  .lk .stat .sub { font-size:11px; color:#8b949e; font-weight:400; }
  .lk .ops { margin-top:10px; overflow-x:auto; }
  .lk .ops table { width:100%; border-collapse:collapse; font-size:12px; min-width:600px; }
  .lk .ops th { text-align:left; color:#8b949e; font-weight:500; padding:4px 6px; border-bottom:1px solid #24314a; white-space:nowrap; }
  .lk .ops td { padding:4px 6px; border-bottom:1px solid #1c2638; white-space:nowrap; }
  .posacc { background:#0e1525; border:1px solid #24314a; border-radius:8px; padding:10px 12px; margin-top:12px; }
  .posacc + .posacc { margin-top:14px; border-top:2px solid #1f6feb; }
  .posacc h3 { margin:0 0 4px; color:#9fb2cf; }
  .grpblock { border:1px solid #1f2f4a; border-radius:6px; margin-top:10px; overflow:hidden; }
  .grpblock:first-child { margin-top:8px; }
  .grphead { display:flex; gap:14px; flex-wrap:wrap; font-size:12px; color:#8b949e; padding:6px 10px; background:#0c1422; border-bottom:1px solid #1f2f4a; }
  .grphead b { color:#e6edf3; }
  .grpblock .ops { margin-top:0; }
  .remain { background:#1f6feb; color:#fff; font-weight:600; padding:2px 10px; border-radius:12px; }
  .remain.neg { background:#a03636; }
  .remain b { color:#fff; }
  .accsum { display:flex; gap:10px; flex-wrap:wrap; font-size:12px; color:#8b949e; margin-top:6px; }
  .accsum b { color:#e6edf3; }
  .deals-toolbar { display:flex; align-items:center; gap:12px; margin-bottom:10px; flex-wrap:wrap; }
  .deals-table { width:100%; border-collapse:collapse; font-size:12px; min-width:0; }
  .deals-table th { text-align:left; color:#8b949e; font-weight:500; padding:6px; border-bottom:1px solid #24314a; white-space:nowrap; }
  .deals-table td { padding:4px 6px; border-bottom:1px solid #1c2638; white-space:normal; vertical-align:top; }
  .deals-table td.bind-cell, .deals-table td.nw { white-space:nowrap; }
  .deals-table .drow2 { background:#101727; }
  .deals-table input, .deals-table select { background:#0e1525; color:#e6edf3; border:1px solid #2c3a55; border-radius:4px; padding:3px 5px; font-size:12px; width:100%; box-sizing:border-box; }
  .deals-table input[type=date] { color-scheme:dark; }
  .deals-scroll { overflow-x:auto; }
  .btn-save { background:#238636; color:#fff; border:none; border-radius:5px; padding:5px 10px; font-size:12px; cursor:pointer; white-space:nowrap; }
  .btn-save:hover { background:#2ea043; }
  .deal-form-card { border-color:#1f6feb; display:block; }
  .deal-form-card .dlg-title { font-size:14px; font-weight:600; margin-bottom:10px; color:#b8c7e0; }
  .deal-form-card .dlg-footer { margin-top:10px; text-align:right; }
  .deal-totblock { margin-bottom:10px; padding:7px 10px; background:#0e1525; border:1px solid #24314a; border-radius:6px; font-size:12px; }
  .deal-head { display:flex; align-items:center; gap:14px; flex-wrap:wrap; margin-bottom:8px; cursor:pointer; user-select:none; }
  .deal-head .spacer { flex:1; }
  .deal-card .fold { display:inline-block; width:14px; text-align:center; color:#8b949e; font-size:12px; }
  .deal-card:not(.collapsed) .fold::after { content:'▾'; }
  .deal-card.collapsed .fold::after { content:'▸'; }
  .deal-card.collapsed .deal-body { display:none; }
  .deal-actions { display:flex; gap:8px; margin-bottom:8px; flex-wrap:wrap; }
  .deal-pnl { font-weight:700; font-size:14px; white-space:nowrap; }
  .btn-del { background:#a03636; color:#fff; border:none; border-radius:5px; padding:5px 10px; font-size:12px; cursor:pointer; }
  .btn-del:hover { background:#c14f4f; }
  .legpnl { font-variant-numeric:tabular-nums; }
  .deal-avg { padding:6px 6px 2px; font-size:12px; color:#8b949e; }
  .deal-status { display:inline-block; font-size:11px; font-weight:700; padding:2px 9px; border-radius:10px; }
  .deal-status.open { background:#12351c; color:#4ad06e; border:1px solid #238636; }
  .deal-status.closed { background:#3a1d1d; color:#ffb4b4; border:1px solid #7d3434; }
  .btn-close-deal { background:#a03636; color:#fff; border:none; border-radius:5px; padding:5px 10px; font-size:12px; cursor:pointer; }
  .btn-close-deal:hover { background:#c14f4f; }
  .btn-mini { background:#30363d; color:#c9d1d9; border:none; border-radius:4px; padding:1px 7px; font-size:11px; cursor:pointer; margin-left:4px; }
  .btn-mini:hover { background:#484f58; }
  .side { font-size:10px; margin-left:3px; }
  .side.buy { color:#3fb950; }
  .side.sell { color:#f85149; }
  .btn-bind { background:#1f6feb; color:#fff; border:none; border-radius:5px; padding:4px 8px; font-size:11px; cursor:pointer; white-space:nowrap; }
  .btn-bind:hover { background:#388bfd; }
  .btn-bind.bound { background:#6e7681; }
  .bind-cell { display:flex; align-items:center; gap:6px; white-space:nowrap; }
  .bind-cell select { background:#0e1525; color:#e6edf3; border:1px solid #2c3a55; border-radius:4px; padding:3px 5px; font-size:11px; max-width:130px; }
  .bind-cell .bound-tag { color:#4ad06e; font-size:11px; font-weight:600; }
  .deal-note { font-size:11px; color:#8b949e; padding:4px 6px; }
  footer { margin-top:14px; color:#8b949e; font-size:11px; }
  .ct { background:#0f1721; border:1px solid #1f2a3d; border-radius:8px; padding:12px 14px; margin-bottom:14px; }
  .ct h2 { font-size:14px; margin:0 0 10px; color:#b8c7e0; }
  .ct .ops table { width:100%; border-collapse:collapse; font-size:12px; min-width:600px; }
  .ct .ops th { text-align:left; color:#8b949e; font-weight:500; padding:4px 6px; border-bottom:1px solid #24314a; white-space:nowrap; }
  .ct .ops td { padding:4px 6px; border-bottom:1px solid #1c2638; white-space:nowrap; }
  .ct .sub-inline { color:#8b949e; font-size:11px; }
  button.refresh { background:#238636; color:#fff; border:none; border-radius:6px; padding:7px 14px; font-size:13px; cursor:pointer; }
  button.refresh:hover { background:#2ea043; }
  button.refresh:disabled { opacity:.6; cursor:default; }
  a.dl-refresh { display:inline-block; background:#161d2b; border:1px solid #283349; color:#8b949e; text-decoration:none; border-radius:6px; padding:7px 12px; font-size:12px; margin-right:8px; }
  a.dl-refresh:hover { color:#58a6ff; border-color:#283349; }
</style>
</head>
<body>
<div style="max-width:1700px;margin:0 auto;">
  <div class="header">
    <div class="h-left">
      <h1>Терминал MOEX Forex <span class="sub" id="sub">Загрузка...</span></h1>
    </div>
    <div class="h-center">
      <span class="sub" id="usd">USD: —</span>
    </div>
    <div class="h-right">
      <a class="dl-refresh" href="/download/win-app" title="Мини-приложение для Windows (без сделок, поверх всех окон)">Win-мини</a>
      <button class="refresh" id="btn" onclick="doRefresh()">Обновить</button>
    </div>
  </div>
  <div class="tabs" id="tabs">
    <button class="tab active" data-tab="deals" onclick="switchTab('deals')">Сделки</button>
    <button class="tab" data-tab="fund" onclick="switchTab('fund')">Фандинг</button>
  </div>
  <div class="tabpane active" data-pane="deals">
    <div class="deals-toolbar">
      <button class="refresh" onclick="dealNew()">Новая сделка</button>
      <select id="deal-type-select" style="display:none;background:#0e1525;color:#e6edf3;border:1px solid #2c3a55;border-radius:4px;padding:6px 8px;font-size:12px;"></select>
      <button class="refresh" id="dealCreateBtn" style="display:none;background:#1f6feb;" onclick="dealCreate()">Создать</button>
      <button class="refresh" id="dealCancelBtn" style="display:none;background:#6e7681;" onclick="dealCancelNew()">Отмена</button>
      <span class="sub" id="deals-status"></span>
    </div>
    <div id="deals-wrap"></div>
  </div>
  <div class="tabpane" data-pane="fund">
    <div id="err"></div>
    <div class="card" id="card"></div>
    <footer>Данные: MOEX ISS (markets/swaprates), фандинг в рублях без учёта лота. Сводка фандингов обновляется 1 раз в час.</footer>
  </div>
  <div id="lk-panes"></div>
  <div id="lf-panes"></div>
  <div id="ct-panes"></div>
<script>
function fmt(v) {
  if (v === null || v === undefined || isNaN(Number(v)) || v === 0) return '—';
  return Number(v).toLocaleString('ru-RU', { maximumFractionDigits: 2 }) + ' ₽';
}

function fmtDelta(v) {
  if (v === null || v === undefined || isNaN(Number(v))) return '—';
  const n = Number(v);
  return (n > 0 ? '+' : '') + n.toLocaleString('ru-RU', { maximumFractionDigits: 2 }) + ' ₽';
}

function cls(v) {
  if (v === null || v === undefined || isNaN(Number(v))) return 'flat';
  const n = Number(v);
  return n > 0 ? 'pos' : (n < 0 ? 'neg' : 'flat');
}

function staleAge(u) {
  // u: 'YYYY-MM-DD HH:MM:SS MSK' → возраст в минутах (сервер и клиент в МСК — парсим как локальное время)
  if (!u) return null;
  const m = u.match(/^(\\d{4})-(\\d{2})-(\\d{2}) (\\d{2}):(\\d{2}):(\\d{2})/);
  if (!m) return null;
  const t = new Date(+m[1], +m[2] - 1, +m[3], +m[4], +m[5], +m[6]).getTime();
  if (isNaN(t)) return null;
  return Math.max(0, Math.round((Date.now() - t) / 60000));
}

function render(data, updated, error, usd, stale) {
  const u = updated || '';
  const age = staleAge(u);
  const staleTxt = (stale || age > 3)
    ? '<span class="stale-badge" title="Данные не обновлялись">⚠ данные устарели' + (age !== null ? ' ' + age + ' мин' : '') + '</span>'
    : '';
  document.getElementById('sub').innerHTML = u
    ? '(' + u.replace(/:\\d{2} MSK$/, '') + ')' + staleTxt
    : staleTxt;
  document.getElementById('usd').textContent = (usd !== null && usd !== undefined && !isNaN(Number(usd))
    ? 'USD: ' + Number(usd).toLocaleString('ru-RU', { maximumFractionDigits: 2 }) + ' ₽' : 'USD: —');
  const err = document.getElementById('err');
  err.innerHTML = error ? '<div class="err">' + error + '</div>' : '';

  const byGroup = {};
  data.forEach(d => { (byGroup[d.group] = byGroup[d.group] || []).push(d); });

  const card = document.getElementById('card');
  card.innerHTML = '';
  const isStale = !!(stale || age > 3);
  card.classList.toggle('stale', isStale);
  for (const [g, items] of Object.entries(byGroup)) {
    const sec = document.createElement('div');
    sec.style.gridColumn = '1 / -1';
    sec.style.marginTop = '6px';
    sec.style.color = '#8b949e';
    sec.style.fontSize = '13px';
    sec.style.fontWeight = '600';
    sec.textContent = g;
    card.appendChild(sec);
    items.forEach(d => {
      const el = document.createElement('div');
      el.className = 'item' + (isStale ? ' stale' : '');
      el.innerHTML =
        '<div class="head"><a class="name" href="' + d.url + '" target="_blank" rel="noopener">' + d.title + '</a>' +
        '<a class="group" href="' + d.contract_url + '" target="_blank" rel="noopener">' + d.secid + '</a></div>' +
        '<div class="val ' + cls(d.last) + (isStale ? ' stale' : '') + '">' + fmt(d.last) +
        (d.yesterday !== null && d.yesterday !== undefined
          ? ' <span class="fund-yest">(' + fmt(d.yesterday) + ')</span>' : '') + '</div>';
      card.appendChild(el);
    });
  }
}

function showErr(msg) {
  document.getElementById('sub').textContent = 'Ошибка соединения: ' + msg;
}

function fmtCs(v) {
  if (v === null || v === undefined || isNaN(Number(v))) return '—';
  return Number(v).toLocaleString('ru-RU', { maximumFractionDigits: 2 }) + ' ₽';
}

function fmtUsd(v) {
  if (v === null || v === undefined || isNaN(Number(v))) return '—';
  return Number(v).toLocaleString('ru-RU', { maximumFractionDigits: 2 }) + ' $';
}

function fmtNum(v) {
  if (v === null || v === undefined || isNaN(Number(v))) return '—';
  return Number(v).toLocaleString('ru-RU', { maximumFractionDigits: 2 });
}

function fmtPx(v) {
  if (v === null || v === undefined || isNaN(Number(v))) return '—';
  return Number(v).toLocaleString('ru-RU', { maximumFractionDigits: 5 });
}

// вкладка «Сделки»: числа без разделителей разрядов, чтобы было удобно копировать в другие программы
function dealFmtCs(v) {
  if (v === null || v === undefined || isNaN(Number(v))) return '—';
  return String(parseFloat(Number(v).toFixed(2))) + ' ₽';
}

function dealFmtNum(v) {
  if (v === null || v === undefined || isNaN(Number(v))) return '—';
  return String(parseFloat(Number(v).toFixed(2)));
}

function dealFmtPx(v) {
  if (v === null || v === undefined || isNaN(Number(v))) return '—';
  return String(parseFloat(Number(v).toFixed(5)));
}

function fmtAlg(t) {
  if (t === 1) return 'Плавающая';
  if (t === 4) return 'Фиксированная';
  return t === undefined || t === null ? '—' : String(t);
}

function stat(k, v, extra, money, sub) {
  return '<div class="stat"><div class="k">' + k + '</div><div class="v ' + (extra || '') + '">' +
    (money ? fmtCs(v) : fmtNum(v)) +
    (sub ? '<div class="sub">' + sub + '</div>' : '') + '</div></div>';
}

const GRP_TITLE = { actions: 'Акции', futures: 'Фьючерсы', currency: 'Валюта' };

function posPrice(it, grp) {
  // Размер позиции = стоимость по цене биржи (фьючерсы — по total_price_futures)
  if (grp === 'futures') return Number(it.total_price_futures) || 0;
  return Number(it.total_price) || 0;
}

function posEntry(it, grp) {
  // Цена входа = стоимость позиции / (количество × лот). Для фьючерсов
  // total_price = position × цена (in_lot=1), для акций — × in_lot.
  const pos = Number(it.position) || 0;
  const tp = Number(it.total_price) || 0;
  const lot = Number(it.in_lot) || 1;
  if (pos === 0 || tp === 0) return null;
  return tp / (Math.abs(pos) * lot);
}

function posRow(it, grp, login, acc) {
  let fundTd = '';
  if (grp === 'futures') {
    if (it.funding_secid) {
      const lastShow = it.funding_last !== null && it.funding_last !== undefined;
      const yestShow = it.funding_yesterday !== null && it.funding_yesterday !== undefined;
      fundTd = '<td class="' + cls(it.funding_last) + '">' + (lastShow ? fmtCs(it.funding_last) : '—') +
        (yestShow ? ' <span style="color:#8b949e;font-size:11px;">(' + fmtCs(it.funding_yesterday) + ')</span>' : '') + '</td>';
    } else {
      fundTd = '<td class="flat">—</td>';
    }
  }
  const entry = posEntry(it, grp);
  // 7.6: позиция нейтральным цветом; 5: фин.рез. позиций серым (площадка — цветом в grphead)
  return '<tr><td><b>' + (it.isin || '—') + '</b></td><td class="flat">' + fmtNum(it.position) + '</td>' +
    '<td class="flat">' + (entry === null ? '—' : fmtPx(entry)) + '</td>' +
    '<td class="flat">' + fmtCs(it.finance_result) + '</td>' +
    '<td>' + fmtCs(posPrice(it, grp)) + '</td>' + fundTd +
    '<td>' + dealBindCell('lk', it.isin, null, login, acc) + '</td></tr>';
}

function posTable(login, acc, pos) {
  if (!pos) return '';
  const ml = pos._maxLoss || {};
  let h = '<div class="posacc"><h3>Лайт Инвест ' + esc(acc) + '</h3>';
  for (const grp of ['actions', 'futures', 'currency']) {
    const items = pos[grp];
    if (!items || !items.length) continue;
    let totFin = 0, totCms = 0, totPrice = 0;
    items.forEach(it => {
      totFin += Number(it.finance_result) || 0;
      totCms += Number(it.cms) || 0;
      totPrice += posPrice(it, grp);
    });
    const fundTh = (grp === 'futures') ? '<th>Фандинг</th>' : '';
    let head = '<div class="grphead"><b>' + GRP_TITLE[grp] + '</b>' +
      '<span>Фин.Рез. <b class="' + cls(totFin) + '">' + fmtCs(totFin) + '</b>';
    // просадка рядом с фин.рез., лимиты убраны из заголовка
    const m = ml[grp];
    if (m && m.max_loss !== null && m.max_loss !== undefined) {
      head += ' <span class="sub">(Просадка ' + fmtCs(m.max_loss) + ')</span>';
    }
    head += '</span>';
    // комиссия — только если не 0
    if (totCms !== 0) head += '<span>Комиссия <b>' + fmtCs(totCms) + '</b></span>';
    head += '<span style="margin-left:auto;">Позиция <b>' + fmtCs(totPrice) + '</b></span></div>';
    h += '<div class="grpblock">' + head + '<div class="ops"><table><tr><th>Инстр.</th><th>Позиция</th><th>Цена</th><th>Фин.рез.</th><th>Позиция (₽)</th>' + fundTh + '<th>Сделка</th></tr>' +
      items.map(it => posRow(it, grp, login, acc)).join('') + '</table></div></div>';
  }
  return h + '</div>';
}

function esc(s) {
  return String(s == null ? '' : s)
    .replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

function levClass(l) {
  // 0..4.6 жёлтый, 4.6..4.7 серый, >4.7 красный
  if (l === null || l === undefined || isNaN(Number(l))) return 'flat';
  const n = Number(l);
  if (n < 4.6) return 'warn';
  if (n <= 4.7) return 'flat';
  return 'neg';
}

function renderLkAcc(d, stale) {
  const statV = (k, vHtml, extra) =>
    '<div class="stat"><div class="k">' + k + '</div><div class="v ' + (extra || '') + '">' + vHtml + '</div></div>';
  // 7.1: разница по балансу в той же строке
  const balDiff = (d.balance === null || d.balance === undefined || d.realBalance === null || d.realBalance === undefined)
    ? null : d.balance - d.realBalance;
  const balHtml = fmtCs(d.balance) +
    (balDiff === null ? '' : ' <span class="sub">(' + fmtDelta(balDiff) + ')</span>');
  // 7.2: плечо в той же строке, увеличенным шрифтом и цветом по значению
  const levShown = (d.leverage !== null && d.leverage !== undefined);
  const posHtmlTop = fmtCs(d.totalPosition) +
    (levShown ? ' <span class="sub lev">(плечо <b class="' + levClass(d.leverage) + '">' + fmtNum(d.leverage) + '</b>)</span>' : '');

  // 7.3: вчерашний фандинг в той же строке, пэйаут убран
  let totFund = 0, totFundYest = 0, fundAny = false;
  for (const acc of (d.accounts || [])) {
    const accPos = d.positions ? d.positions[acc] : null;
    if (!accPos) continue;
    for (const grp of ['actions', 'futures', 'currency']) {
      for (const it of (accPos[grp] || [])) {
        if (it.funding_last !== null && it.funding_last !== undefined) {
          totFund += Number(it.funding_last) || 0; fundAny = true;
        }
        if (it.funding_yesterday !== null && it.funding_yesterday !== undefined) {
          totFundYest += Number(it.funding_yesterday) || 0;
        }
      }
    }
  }
  const fundHtml = (fundAny ? fmtCs(totFund) : '—') +
    (fundAny ? ' <span class="sub">(' + fmtCs(totFundYest) + ')</span>' : '');

  // пэйаут показываем у никнейма в правом верхнем углу блока
  const payHtml = (d.payout !== null && d.payout !== undefined && d.payout > 0)
    ? Math.round(d.payout * 100) + '%'
    : null;

  let blocks = '';
  if (d.positions) {
    for (const acc of (d.accounts || [])) {
      blocks += posTable(d.login, acc, d.positions[acc]);
    }
  }

  const nick = (d.nickname && d.nickname !== d.login) ? d.nickname : d.login;
  const staleBadge = stale
    ? '<span class="stale-badge" title="Данные ЛК не обновлялись">⚠ данные устарели</span>'
    : '';
  return '<div class="lk' + (stale ? ' stale' : '') + '">' +
    '<h2 class="lk-head"><span class="nick">' + esc(nick) + '</span>' +
    (payHtml ? '<span class="pay">Пэйаут: ' + payHtml + '</span>' : '') +
    staleBadge + '</h2>' +
    '<div class="stats">' +
    statV('Баланс', balHtml, '') +
    statV('Суммарная позиция', posHtmlTop, '') +
    statV('Фандинг', fundHtml, fundAny ? cls(totFund) : '') +
    '</div>' +
    blocks +
    '</div>';
}

async function tickLk() {
  try {
    const r = await fetch('/api/lk');
    const j = await r.json();
    buildLkTabs(j.accounts || []);
  } catch (e) {}
}

async function tickTd() {
  try {
    const r = await fetch('/api/td');
    const j = await r.json();
    buildTdTabs(j);
  } catch (e) {}
}

function sortTabs() {
  const tabs = document.getElementById('tabs');
  const order = ['deals', 'moex', 'forex', 'fund'];
  const kids = Array.from(tabs.children);
  kids.sort((a, b) => {
    const ia = order.indexOf(a.getAttribute('data-tab'));
    const ib = order.indexOf(b.getAttribute('data-tab'));
    return (ia < 0 ? 99 : ia) - (ib < 0 ? 99 : ib);
  });
  kids.forEach(k => tabs.appendChild(k));
}

function buildLkTabs(accounts) {
  const tabs = document.getElementById('tabs');
  const panes = document.getElementById('lk-panes');
  let tb = tabs.querySelector('[data-tab="moex"]');
  if (!tb) {
    tb = document.createElement('button');
    tb.className = 'tab';
    tb.setAttribute('data-tab', 'moex');
    tb.textContent = 'MOEX';
    tb.onclick = function() { switchTab('moex'); };
    tabs.appendChild(tb);
  }
  let pan = panes.querySelector('[data-pane="moex"]');
  if (!pan) {
    pan = document.createElement('div');
    pan.className = 'tabpane';
    pan.setAttribute('data-pane', 'moex');
    panes.appendChild(pan);
  }
  pan.innerHTML = renderLkAll(accounts);
  sortTabs();
  restoreTab();
}

function renderLkAll(accounts) {
  let html = '';
  let updated = null;
  for (const acc of accounts) {
    const d = acc.data;
    if (acc.updated && (!updated || acc.updated > updated)) updated = acc.updated;
    if (!d) {
      html += acc.error
        ? '<div class="err">ЛК: ' + esc(acc.error) + '</div>'
        : '<div class="sub">Нет данных</div>';
      continue;
    }
    html += renderLkAcc(d, !!(acc.stale));
  }
  if (updated) html += '<div class="sub">Обновлено: ' + updated + '</div>';
  return html;
}

function buildTdTabs(j) {
  const data = j.data || null;
  const stale = !!j.stale;
  const tabs = document.getElementById('tabs');
  const panes = document.getElementById('lf-panes');
  let tb = tabs.querySelector('[data-tab="td"]');
  if (!tb) {
    tb = document.createElement('button');
    tb.className = 'tab';
    tb.setAttribute('data-tab', 'td');
    tb.textContent = 'Diary';
    tb.onclick = function() { switchTab('td'); };
    tabs.appendChild(tb);
  }
  let pan = panes.querySelector('[data-pane="td"]');
  if (!pan) {
    pan = document.createElement('div');
    pan.className = 'tabpane';
    pan.setAttribute('data-pane', 'td');
    panes.appendChild(pan);
  }
  let html = '';
  if (j.error) {
    html = '<div class="err">TD: ' + esc(j.error) + '</div>';
  } else if (!data) {
    html = '<div class="sub">Нет данных</div>';
  } else {
    html += renderTdPositions(data.positions || [], stale);
    for (const a of (data.accounts || [])) html += renderTdAcc(a, stale);
    if (j.updated) html += '<div class="sub">Обновлено: ' + j.updated + '</div>';
  }
  pan.innerHTML = html;
  sortTabs();
  restoreTab();
}

function renderTdAcc(a, stale) {
  const bal = (a.balance === undefined || a.balance === null) ? '—' : fmtNum(a.balance);
  const staleBadge = stale
    ? '<span class="stale-badge" title="Данные TD не обновлялись">⚠</span>' : '';
  const trades = (a.trades || []).slice(0, 12).map(t =>
    '<tr><td><b>' + esc(t.symbol || '—') + '</b></td>' +
    '<td>' + esc(t.date || '') + '</td>' +
    '<td class="' + (t.side === 'buy' ? 'pos' : 'neg') + '">' + esc(t.side || '') + '</td>' +
    '<td>' + fmtNum(t.quantity || t.total_buy || 0) + '</td>' +
    '<td class="' + cls(t.profit) + '">' + fmtCs(t.profit === null || t.profit === undefined ? 0 : t.profit) + '</td>' +
    '<td class="' + cls(t.profit_perc) + '">' + fmtNum(t.profit_perc) + '%</td></tr>'
  ).join('');
  return '<div class="lk' + (stale ? ' stale' : '') + '">' +
    '<h2 class="lk-head"><span class="nick">' + esc((a.market || '?').toUpperCase()) + '</span>' +
    '<span class="sub">' + esc(a.masked_token || '') + '</span>' + staleBadge +
    '<button class="fold" onclick="toggleLk(this)"></button></h2>' +
    '<div class="stats">' +
    '<div class="stat"><div class="k">Баланс</div><div class="v">' + bal + '</div></div>' +
    '</div>' +
    (trades ? '<div class="ops"><table><tr><th>Символ</th><th>Дата</th><th>Сторона</th><th>Объём</th><th>P&L</th><th>P&L %</th></tr>' + trades + '</table></div>' : '') +
    '</div>';
}

function renderTdPositions(positions, stale) {
  if (!positions.length) return '';
  const staleBadge = stale
    ? '<span class="stale-badge" title="Данные TD не обновлялись">⚠</span>' : '';
  const rows = positions.map(p => {
    const side = p.side === 'sell' ? 'продажа' : 'покупка';
    const sideCls = p.side === 'sell' ? 'neg' : 'pos';
    const profit = p.finrez === undefined || p.finrez === null ? '—' :
      '<span class="' + cls(p.finrez) + '">' + fmtCs(p.finrez) + '</span>';
    const perc = p.profit_perc === null || p.profit_perc === undefined ? '—' :
      '<span class="' + cls(p.profit_perc) + '">' + fmtNum(p.profit_perc) + '%</span>';
    return '<tr><td><b>' + esc(p.symbol || '—') + '</b></td>' +
      '<td>' + esc(p.board || '') + '</td>' +
      '<td>' + esc(p.key_name || '') + '</td>' +
      '<td>' + esc(p.exchange || '') + '</td>' +
      '<td class="' + sideCls + '">' + side + '</td>' +
      '<td>' + fmtNum(p.pos || 0) + '</td>' +
      '<td>' + (p.avg_entry === undefined || p.avg_entry === null ? '—' : fmtNum(p.avg_entry)) + '</td>' +
      '<td>' + profit + '</td>' +
      '<td>' + perc + '</td></tr>';
  }).join('');
  return '<div class="lk' + (stale ? ' stale' : '') + '">' +
    '<h2 class="lk-head"><span class="nick">PROP (позиции)</span>' +
    '<button class="fold" onclick="toggleLk(this)"></button>' + staleBadge + '</h2>' +
    '<div class="ops"><table><tr><th>Символ</th><th>Биржа</th><th>Счёт</th><th>Площадка</th>' +
    '<th>Сторона</th><th>Позиция</th><th>Ср. цена</th><th>Фин.рез</th><th>P&L %</th></tr>' + rows + '</table></div>' +
    '</div>';
}

function toggleLk(btn) {
  const card = btn.closest('.lk');
  if (card) card.classList.toggle('collapsed');
}

function buildCtTabs(entries) {
  const tabs = document.getElementById('tabs');
  const panes = document.getElementById('ct-panes');
  if (!entries.length) return;
  let tb = tabs.querySelector('[data-tab="forex"]');
  if (!tb) {
    tb = document.createElement('button');
    tb.className = 'tab';
    tb.setAttribute('data-tab', 'forex');
    tb.textContent = 'Forex';
    tb.onclick = function() { switchTab('forex'); };
    tabs.appendChild(tb);
  }
  let pan = panes.querySelector('[data-pane="forex"]');
  if (!pan) {
    pan = document.createElement('div');
    pan.className = 'tabpane';
    pan.setAttribute('data-pane', 'forex');
    panes.appendChild(pan);
  }
  let html = '';
  let updated = null;
  for (const en of entries) {
    if (en.updated && (!updated || en.updated > updated)) updated = en.updated;
    const d = en.data;
    if (!d) {
      html += en.error
        ? '<div class="err">Forex: ' + esc(en.error) + '</div>'
        : '<div class="sub">Нет данных</div>';
      continue;
    }
    html += renderCtGroup(d);
  }
  if (updated) html += '<div class="sub">Обновлено: ' + updated + '</div>';
  pan.innerHTML = html;
  sortTabs();
  restoreTab();
}

function renderCtGroup(d) {
  let h = '';
  for (const a of (d.accounts || [])) {
    h += renderCtAcc(a);
  }
  return h;
}

function renderCtAcc(a) {
  const hasData = (a.positions && a.positions.length) || a.balance != null;
  const staleBadge = a.error
    ? '<span class="stale-badge" title="' + esc(a.error) + '">⚠ не обновлялось</span>'
    : '';
  if (a.error && !hasData) {
    return '<div class="ct"><h2>' + esc(a.login || '') + '</h2>' +
      '<div class="err">' + esc(a.error) + '</div></div>';
  }
  const posRows = (a.positions || []).map(p => {
    const side = p.side === 'buy' ? 'покупка' : 'продажа';
    const sideCls = p.side === 'buy' ? 'pos' : 'neg';
    const pnlVal = (p.netPnl !== null && p.netPnl !== undefined) ? p.netPnl
                 : (p.grossPnl !== null && p.grossPnl !== undefined ? p.grossPnl : null);
    const pnlCell = pnlVal === null ? '—'
      : '<span class="' + cls(pnlVal) + '">' + fmtUsd(pnlVal) + '</span>' +
        (p.pnlRub === null || p.pnlRub === undefined ? '' : ' <span class="sub-inline">(' + fmtCs(p.pnlRub) + ')</span>');
    return '<tr><td><b>' + esc(p.symbol || '—') + '</b></td>' +
      '<td class="' + sideCls + '">' + side + '</td>' +
      '<td>' + fmtNum(p.volumeUnits) + '</td>' +
      '<td>' + fmtPx(p.price) + '</td>' +
      '<td>' + (p.swap === null || p.swap === undefined ? '—' : fmtUsd(p.swap)) + '</td>' +
      '<td>' + pnlCell + '</td>' +
      '<td>' + (p.openTime ? esc(p.openTime) : '—') + '</td>' +
      '<td>' + dealBindCell('ct', null, p.symbol) + '</td></tr>';
  }).join('');

  return '<div class="ct' + (a.error ? ' stale' : '') + '"><h2>cTrader — ' + esc(a.login) + staleBadge + '</h2>' +
    '<div class="stats">' +
    statUsd('Баланс', a.balance, '', true) +
    statUsd('Эквити', a.equity, cls(a.totalNetPnl), true) +
    stat('Позиции', a.positionCount, '', false) +
    statUsd('P&L', a.totalNetPnl, cls(a.totalNetPnl), true) +
    statUsd('Своп', a.totalSwap, cls(a.totalSwap), true) +
    '</div>' +
    (a.positions && a.positions.length ?
      '<div class="ops"><table><tr><th>Инструмент</th><th>Сторона</th><th>Объём (лот)</th><th>Цена</th><th>Своп</th><th>P&L</th><th>Открыта (МСК)</th><th>Сделка</th></tr>' +
      posRows + '</table></div>' : '') +
    '</div>';
}

function statUsd(k, v, extra, money) {
  return '<div class="stat"><div class="k">' + k + '</div><div class="v ' + (extra || '') + '">' +
    (money ? fmtUsd(v) : fmtNum(v)) + '</div></div>';
}

async function tickCt() {
  try {
    const r = await fetch('/api/ct');
    const j = await r.json();
    buildCtTabs(j.entries || []);
  } catch (e) {}
}

function applyTab(name) {
  document.querySelectorAll('#tabs .tab').forEach(t =>
    t.classList.toggle('active', t.getAttribute('data-tab') === name));
  document.querySelectorAll('.tabpane').forEach(p =>
    p.classList.toggle('active', p.getAttribute('data-pane') === name));
}

function switchTab(name) {
  localStorage.setItem('moexTab', name);
  applyTab(name);
}

function restoreTab() {
  let name = localStorage.getItem('moexTab');
  // по умолчанию открываем MOEX, если вкладка ещё не построена
  if (!name || !document.querySelector('[data-tab="' + name + '"]')) {
    if (document.querySelector('[data-tab="moex"]')) {
      name = 'moex';
    } else {
      name = 'deals';
    }
  }
  applyTab(name);
}

async function tick(manual) {
  const url = manual ? '/api/refresh' : '/api/funding';
  if (manual) {
    const btn = document.getElementById('btn');
    btn.disabled = true;
    btn.textContent = 'Обновление...';
  }
  try {
    const r = await fetch(url);
    const j = await r.json();
    render(j.data, j.updated, j.error, j.usd, j.stale);
  } catch (e) {
    showErr(e);
  } finally {
    if (manual) {
      const btn = document.getElementById('btn');
      btn.disabled = false;
      btn.textContent = 'Обновить';
    }
  }
}

async function doRefresh() { await tick(true); }

let dealState = { types: [], deals: [], usd: null };
let openDealsCache = [];  // открытые сделки {id, typeId, title}

function numOrNull(v) {
  if (v === null || v === undefined || v === '') return null;
  const n = Number(String(v).replace(',', '.'));
  return isNaN(n) ? null : n;
}

function fmtDeltaPnl(v) {
  return (v > 0 ? '+' : '') + Number(v).toFixed(2) + ' $';
}

function clsPnl(v) {
  if (v === null || isNaN(v)) return 'flat';
  return v > 0 ? 'pos' : (v < 0 ? 'neg' : 'flat');
}

function dealTypeTitle(typeId) {
  const t = dealState.types.find(x => x.id === typeId);
  return t ? (t.title || t.id) : (typeId || '—');
}

function dealStatusBadge(status) {
  if (status === 'Закрыта') return '<span class="deal-status closed">Закрыта</span>';
  return '<span class="deal-status open">Активна</span>';
}

function dealOpenDeals() {
  return (dealState.deals || []).filter(d => d.status === 'Активна');
}

// позиция привязана? возвращает {dealId, legKey, deal} или null
function dealFindBound(src, isin, symbol) {
  const key = (symbol || isin || '').toUpperCase();
  for (const d of (dealState.deals || [])) {
    for (const leg of (d.legs || [])) {
      const p = (leg.positions || []).find(x =>
        x.src === src && (x.symbol || x.isin || '').toUpperCase() === key);
      if (p) return { dealId: d.id, legKey: leg.key, deal: d };
    }
  }
  return null;
}

function dealLegLabel(ld) {
  return ld && ld.title ? ld.title : (ld && ld.ticker ? ld.ticker : (ld && ld.key ? ld.key : '—'));
}

function dealPositionLabel(pos) {
  if (pos.src === 'ct') return pos.symbol || '—';
  return pos.isin || '—';
}

function dealToggle(id) {
  const el = document.querySelector('.deal-card[data-id="' + id + '"]');
  if (el) el.classList.toggle('collapsed');
}

function dealRender() {
  const wrap = document.getElementById('deals-wrap');
  if (!wrap) return;
  const deals = (dealState.deals || []).slice().sort((a, b) => (b.id || 0) - (a.id || 0));
  openDealsCache = dealOpenDeals();
  if (!deals.length) {
    wrap.innerHTML = '<div class="deal-note">Нет сделок. Нажмите «Новая сделка».</div>';
    return;
  }
  let html = '';
  for (const d of deals) {
    let rows = '';
    let total = 0, any = false;
    for (const leg of (d.legs || [])) {
      const legSide = (leg.side || 'buy') === 'buy' ? 'buy' : 'sell';
      const sideArrow = '<span class="side ' + legSide + '">' + (legSide === 'buy' ? '&#9650;' : '&#9660;') + '</span>';
      const posCells = (leg.positions || []).map(p => {
        const label = esc(dealPositionLabel(p)) + ' ' + sideArrow;
        // Всегда отображаем данные позиции, даже если closed — показываем "—" при отсутствии данных
        const qty = p.qty === null || p.qty === undefined ? '—' : dealFmtNum(p.qty);
        const entry = p.entry === null || p.entry === undefined ? '—' : dealFmtPx(p.entry);
        const cur = p.current === null || p.current === undefined ? '—' : dealFmtPx(p.current);
        const pnl = p.pnl === null || p.pnl === undefined ? '—' :
          '<span class="' + cls(p.pnl) + '">' + dealFmtCs(p.pnl) + '</span>';
        return '<div>' + label + ' · ' + qty + ' @ ' + entry +
          ' · тек. ' + cur + ' · ' + pnl + '</div>';
      }).join('') || '<span class="deal-note">— не привязана</span>';
      const legPnl = leg.pnlRub === null || leg.pnlRub === undefined ? '—' :
        '<span class="' + cls(leg.pnlRub) + '">' + dealFmtCs(leg.pnlRub) + '</span>';
      const legEntry = leg.avgEntry === null || leg.avgEntry === undefined ? '—' : dealFmtPx(leg.avgEntry);
      const legCur = leg.current === null || leg.current === undefined ? '—' : dealFmtPx(leg.current);
      rows += '<tr><td><b>' + esc(leg.key) + '</b></td><td>' + posCells + '</td>' +
        '<td class="nw">' + legEntry + '</td><td class="nw">' + legCur + '</td>' +
        '<td class="nw ' + clsPnl(leg.pnlRub) + '">' + legPnl + '</td></tr>';
      if (leg.pnlRub !== null && leg.pnlRub !== undefined) { total += leg.pnlRub; any = true; }
    }
    if (d.pnlRub !== null && d.pnlRub !== undefined) { total = d.pnlRub; any = true; }
    const isClosed = d.status === 'Закрыта';
    const head = '<div class="deal-head" onclick="dealToggle(' + d.id + ')">' +
      '<span class="fold"></span>' +
      '<b>#' + d.id + ' — ' + esc(dealTypeTitle(d.typeId)) + '</b>' +
      dealStatusBadge(d.status) +
      '<span class="sub">' + esc(d.openedAt || '') + (d.closedAt ? ' → ' + esc(d.closedAt) : '') + '</span>' +
      '<span class="spacer"></span>' +
      '<span class="deal-pnl ' + clsPnl(any ? total : null) + '">' + (any ? dealFmtCs(total) : '—') + '</span></div>';
    let actions = '<button class="btn-del" onclick="event.stopPropagation();dealDelete(' + d.id + ')">Удалить</button>';
    if (d.status === 'Активна') {
      actions = '<button class="btn-close-deal" onclick="event.stopPropagation();dealClose(' + d.id + ')">закрыть Сделку</button> ' + actions;
    }
    if (isClosed && d.commission !== null && d.commission !== undefined) {
      actions = '<button class="btn-mini" onclick="event.stopPropagation();dealSetCommission(' + d.id + ')">Комиссия: ' +
        dealFmtCs(d.commission) + '</button> ' + actions;
    }
    const totalLine = '<div class="deal-avg">Точка входа: <b>' + (d.entryPoint !== null && d.entryPoint !== undefined ? dealFmtPx(d.entryPoint) : '—') + '</b>' +
      (isClosed ? ' &nbsp;·&nbsp; Точка выхода: <b>' + (d.exitPoint !== null && d.exitPoint !== undefined ? dealFmtPx(d.exitPoint) : '—') + '</b>' : '') +
      ' &nbsp;·&nbsp; Итог по сделке: <b class="' + clsPnl(total) + '">' +
      (any ? dealFmtCs(total) : '—') + '</b>' +
      (isClosed ? ' &nbsp;·&nbsp; Комиссия: <b>' +
        (d.commission !== null && d.commission !== undefined ? dealFmtCs(d.commission) : '—') + '</b> <button class="btn-mini" onclick="event.stopPropagation();dealSetCommission(' + d.id + ')">изменить</button>' : '') +
      '</div>';
    html += '<div class="card deal-card' + (isClosed ? ' collapsed' : '') + '" data-id="' + d.id + '">' + head + '<div class="deal-actions">' + actions + '</div>' +
      '<div class="deal-body"><div class="deals-scroll"><table class="deals-table"><thead><tr><th>Нога</th><th>Позиции</th>' +
      '<th>Ср. вход</th><th>Текущая</th><th>PnL</th></tr></thead><tbody>' +
      rows + '</tbody></table></div>' + totalLine + '</div></div>';
  }
  wrap.innerHTML = html;
}

function dealNew() {
  const sel = document.getElementById('deal-type-select');
  const crt = document.getElementById('dealCreateBtn');
  const can = document.getElementById('dealCancelBtn');
  if (!sel) return;
  if (!dealState.types.length) { alert('Типы сделок не загружены'); return; }
  sel.innerHTML = dealState.types.map(t =>
    '<option value="' + esc(t.id) + '">' + esc(t.title) + '</option>').join('');
  sel.style.display = '';
  crt.style.display = '';
  can.style.display = '';
  sel.focus();
}

function dealCancelNew() {
  document.getElementById('deal-type-select').style.display = 'none';
  document.getElementById('dealCreateBtn').style.display = 'none';
  document.getElementById('dealCancelBtn').style.display = 'none';
}

async function dealCreate() {
  const typeId = document.getElementById('deal-type-select').value;
  if (!typeId) return;
  try {
    const r = await fetch('/api/deals/create', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ typeId: typeId }),
    });
    const j = await r.json();
    if (!j.ok) { alert('Ошибка: ' + (j.error || '')); return; }
    dealCancelNew();
    dealLoad();
  } catch (e) { alert('Ошибка создания сделки'); }
}

async function dealClose(id) {
  try {
    const r = await fetch('/api/deals/close', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ id: id }),
    });
    const j = await r.json();
    if (!j.ok) { alert('Ошибка: ' + (j.error || '')); return; }
    dealLoad();
  } catch (e) { alert('Ошибка закрытия сделки'); }
}

async function dealSetCommission(id) {
  const cur = (dealState.deals.find(x => x.id === id) || {}).commission;
  const prompt = window.prompt('Комиссия по сделке #' + id + ' (рубли):', cur !== null && cur !== undefined ? String(cur) : '');
  if (prompt === null || prompt === '') return;
  const val = prompt.replace(',', '.');
  if (isNaN(parseFloat(val))) { alert('Введите число'); return; }
  try {
    const r = await fetch('/api/deals/commission', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ id: id, commission: parseFloat(val) }),
    });
    const j = await r.json();
    if (!j.ok) { alert('Ошибка: ' + (j.error || '')); return; }
    dealLoad();
  } catch (e) { alert('Ошибка сохранения комиссии'); }
}

async function dealDelete(id) {
  if (!confirm('Удалить сделку #' + id + '?')) return;
  try {
    const r = await fetch('/api/deals/delete', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ id: id }),
    });
    const j = await r.json();
    if (!j.ok) { alert('Ошибка: ' + (j.error || '')); return; }
    dealLoad();
  } catch (e) { alert('Ошибка удаления сделки'); }
}

async function dealBind(src, isin, symbol, login=null, account=null) {
  const sel = document.getElementById('bind-deal-' + (symbol || isin || '') + '-' + src);
  if (!sel) return;
  const dealId = numOrNull(sel.value);
  if (dealId === null) return;
  try {
    const r = await fetch('/api/deals/bind', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ id: dealId, src: src, isin: isin, symbol: symbol, login: login, account: account }),
    });
    const j = await r.json();
    if (!j.ok) { alert('Ошибка: ' + (j.error || '')); return; }
    dealLoad();
  } catch (e) { alert('Ошибка привязки'); }
}

async function dealUnbind(dealId, src, isin, symbol) {
  try {
    const r = await fetch('/api/deals/unbind', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ id: dealId, src: src, isin: isin, symbol: symbol }),
    });
    const j = await r.json();
    if (!j.ok) { alert('Ошибка: ' + (j.error || '')); return; }
    dealLoad();
  } catch (e) { alert('Ошибка отвязки'); }
}

// поле привязки для позиции (MOEX или Forex)
function dealBindCell(src, isin, symbol, login=null, account=null) {
  const key = (symbol || isin || '') + '-' + src;
  const bound = dealFindBound(src, isin, symbol);
  if (bound) {
    return '<div class="bind-cell"><span class="bound-tag">#' + bound.dealId + '</span>' +
      '<button class="btn-bind bound" onclick="dealUnbind(' + bound.dealId + ',\\'' + src + '\\',\\'' +
      esc(isin || '') + '\\',\\'' + esc(symbol || '') + '\\')">Отвязать</button></div>';
  }
  const deals = (dealState.deals || []).slice().sort((a, b) => (b.id || 0) - (a.id || 0));
  // по умолчанию выбираем самую свежую активную сделку — тогда кнопка «Привязать»
  // сразу сработает, даже если пользователь не выбрал сделку вручную
  const activeDeals = deals.filter(d => d.status !== 'Закрыта');
  const defaultId = activeDeals.length ? activeDeals[0].id : (deals.length ? deals[0].id : null);
  const opts = deals.map(d =>
    '<option value="' + d.id + '"' + (d.id === defaultId ? ' selected' : '') + '>#' + d.id + ' ' +
    esc(dealTypeTitle(d.typeId)) +
    (d.status === 'Закрыта' ? ' (закрыта)' : '') + '</option>').join('');
  const bindArgs = "'" + src + "','" + esc(isin || '') + "','" + esc(symbol || '') + "'" +
    (login !== null ? ",'" + esc(login || '') + "'" : '') +
    (account !== null ? ",'" + esc(account || '') + "'" : '');
  return '<div class="bind-cell">' +
    ((dealState.deals || []).length
      ? '<select id="bind-deal-' + key + '"><option value="">Сделку…</option>' + opts + '</select>' +
        '<button class="btn-bind" onclick="dealBind(' + bindArgs + ')">Привязать</button>'
      : '<span class="deal-note">нет сделок</span>') +
    '</div>';
}

function dealLoad() {
  fetch('/api/deals').then(r => r.json()).then(j => {
    dealState.types = j.types || dealState.types;
    dealState.deals = j.deals || [];
    dealState.usd = j.usd;
    dealRender();
    document.getElementById('deals-status').textContent =
      'Курс USD: ' + (j.usd !== null && j.usd !== undefined ? j.usd : '—');
    // перерисовать привязки на вкладках MOEX/Forex
    if (document.querySelector('[data-pane="moex"]')) tickLk();
    if (document.querySelector('[data-pane="forex"]')) tickCt();
  }).catch(() => {
    document.getElementById('deals-status').textContent = 'Ошибка загрузки сделок';
  });
}


tick(false);
tickLk();
tickCt();
tickTd();
dealLoad();
restoreTab();
setInterval(() => tick(false), 30000);
setInterval(() => tickLk(), 60000);
setInterval(() => tickCt(), 60000);
setInterval(() => tickTd(), 300000);
setInterval(() => dealLoad(), 60000);
</script>
</body>
</html>
"""

def _server_cfg():
    cfg_path = os.path.join(BASE_DIR, "config.json")
    if not os.path.exists(cfg_path):
        return {}
    try:
        with open(cfg_path, encoding="utf-8") as f:
            cfg = json.load(f)
    except Exception:
        return {}
    srv = (cfg or {}).get("server")
    return srv if isinstance(srv, dict) else {}


def load_allowed_clients():
    """IP, которым разрешён доступ к интерфейсу.

    По умолчанию — только localhost. Другие адреса перечисляются в
    config.json → server.allowed_clients (или ["*"] для доступа со всех адресов).
    """
    base = {"127.0.0.1", "::1"}
    raw = _server_cfg().get("allowed_clients")
    if not isinstance(raw, list):
        return base
    for item in raw:
        val = str(item).strip()
        if not val:
            continue
        if val == "*":
            return {"*"}
        base.add(val)
    return base


ALLOWED_CLIENTS = load_allowed_clients()


def client_allowed(client):
    return "*" in ALLOWED_CLIENTS or client in ALLOWED_CLIENTS


threading.Thread(target=background, daemon=True).start()
threading.Thread(target=lk_background, daemon=True).start()
threading.Thread(target=ct_background, daemon=True).start()
threading.Thread(target=td_background, daemon=True).start()
threading.Thread(target=tg_background, daemon=True).start()
HOST = _server_cfg().get("host") or "0.0.0.0"
PORT = int(_server_cfg().get("port") or 8642)


def make_handler():
    from http.server import BaseHTTPRequestHandler

    class Handler(BaseHTTPRequestHandler):
        def log_message(self, fmt, *args):
            pass

        def _deny(self):
            self.send_response(403)
            self.end_headers()
            self.wfile.write(b"403 Forbidden")

        def _json(self, obj):
            payload = json.dumps(obj).encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Cache-Control", "no-store")
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)

        def do_GET(self):
            client = self.client_address[0]
            if not client_allowed(client):
                return self._deny()
            from urllib.parse import urlsplit
            self.path = urlsplit(self.path).path
            if self.path in ("/", "/index.html"):
                body = PAGE.encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            elif self.path == "/favicon.svg":
                try:
                    with open(os.path.join(BASE_DIR, "favicon.svg"), "rb") as f:
                        body = f.read()
                    self.send_response(200)
                    self.send_header("Content-Type", "image/svg+xml")
                    self.send_header("Content-Length", str(len(body)))
                    self.end_headers()
                    self.wfile.write(body)
                except OSError:
                    self.send_response(404)
                    self.end_headers()
            elif self.path == "/favicon.png":
                try:
                    with open(os.path.join(BASE_DIR, "favicon.png"), "rb") as f:
                        body = f.read()
                    self.send_response(200)
                    self.send_header("Content-Type", "image/png")
                    self.send_header("Cache-Control", "max-age=86400")
                    self.send_header("Content-Length", str(len(body)))
                    self.end_headers()
                    self.wfile.write(body)
                except OSError:
                    self.send_response(404)
                    self.end_headers()
            elif self.path == "/download/win-app":
                # Мини-приложение для Windows (zip) — отдаём последний собранный
                dist_dir = os.path.join(BASE_DIR, "win-app", "dist")
                zips = []
                try:
                    zips = [f for f in os.listdir(dist_dir) if f.endswith(".zip")]
                except OSError:
                    zips = []
                if not zips:
                    self.send_response(404)
                    self.send_header("Content-Type", "text/plain; charset=utf-8")
                    body = "Архив мини-приложения не найден. Соберите его: cd win-app && npm run dist".encode()
                    self.send_header("Content-Length", str(len(body)))
                    self.end_headers()
                    self.wfile.write(body)
                else:
                    latest = max(zips)
                    try:
                        with open(os.path.join(dist_dir, latest), "rb") as f:
                            body = f.read()
                        self.send_response(200)
                        self.send_header("Content-Type", "application/zip")
                        self.send_header("Content-Disposition", f'attachment; filename="{latest}"')
                        self.send_header("Content-Length", str(len(body)))
                        self.end_headers()
                        self.wfile.write(body)
                    except OSError:
                        self.send_response(404)
                        self.end_headers()
            elif self.path == "/api/funding":
                with lock:
                    self._json(
                        {
                            "data": state["data"] or [],
                            "updated": state["updated"],
                            "error": state["error"],
                            "usd": get_usd_rate_cached(),
                            "stale": funding_stale(),
                        }
                    )
            elif self.path == "/api/refresh":
                self._json(refresh_now())
            elif self.path == "/api/lk":
                with lk_lock:
                    accounts = [
                        {
                            "login": login,
                            "data": st["data"],
                            "updated": st["updated"],
                            "error": st["error"],
                            "stale": (st.get("updated") is None or time.time() - st.get("ts", 0.0) > LK_STALE_TTL),
                        }
                        for login, st in lk_state["accounts"].items()
                    ]
                self._json({"accounts": accounts})
            elif self.path == "/api/lk/refresh":
                self._json({"accounts": lk_refresh_now()})
            elif self.path == "/api/td":
                with td_lock:
                    st = td_state["accounts"]
                    self._json({
                        "data": st.get("data") if isinstance(st, dict) else None,
                        "updated": td_state.get("updated"),
                        "error": td_state.get("error"),
                        "stale": (td_state.get("updated") is None or time.time() - td_state.get("ts", 0.0) > TD_STALE_TTL),
                    })
            elif self.path == "/api/td/refresh":
                self._json({"data": td_refresh_now()})
            elif self.path == "/api/ct":
                with ct_lock:
                    entries = [
                        {"label": label, "data": st["data"], "updated": st["updated"], "error": st["error"]}
                        for label, st in ct_state["accounts"].items()
                    ]
                self._json({"entries": entries})
            elif self.path == "/api/ct/refresh":
                ct_trigger_refresh()
                self._json({"entries": ct_current_entries(), "refreshing": True})
            elif self.path == "/api/deals":
                self._json(build_deals_payload_safe())
            elif self.path == "/api/deals/current":
                try:
                    self._json({
                        "types": deal_types_with_current(),
                        "lkPositions": get_lk_futures_positions(),
                        "goldContracts": gold_contracts_cache["data"] or [],
                        "usd": get_usd_rate_cached(),
                    })
                except Exception:
                    self._json({"ok": False, "error": "refresh failed"})
            else:
                self.send_response(404)
                self.end_headers()
                self.wfile.write(b"404 Not Found")

        def do_POST(self):
            client = self.client_address[0]
            if not client_allowed(client):
                return self._deny()
            if self.path == "/api/deals/save":
                try:
                    length = int(self.headers.get("Content-Length") or 0)
                    deal = json.loads(self.rfile.read(length).decode("utf-8"))
                except Exception:
                    self._json({"ok": False, "error": "Некорректный JSON"})
                    return
                deals = load_deals()
                ids = [d.get("id") for d in deals if isinstance(d.get("id"), int)]
                deal["id"] = max([0] + ids) + 1
                deals.append(deal)
                save_deals(deals)
                self._json({"ok": True, "id": deal["id"]})
            elif self.path == "/api/deals/update":
                try:
                    length = int(self.headers.get("Content-Length") or 0)
                    upd = json.loads(self.rfile.read(length).decode("utf-8"))
                except Exception:
                    self._json({"ok": False, "error": "Некорректный JSON"})
                    return
                deals = load_deals()
                for d in deals:
                    if d.get("id") == upd.get("id") and isinstance(d.get("legs"), list):
                        for leg in d["legs"]:
                            for u in upd.get("legs") or []:
                                if leg.get("key") == u.get("key"):
                                    leg["current"] = u.get("current")
                save_deals(deals)
                self._json({"ok": True})
            elif self.path == "/api/deals/delete":
                try:
                    length = int(self.headers.get("Content-Length") or 0)
                    payload = json.loads(self.rfile.read(length).decode("utf-8"))
                except Exception:
                    self._json({"ok": False, "error": "Некорректный JSON"})
                    return
                deals = load_deals()
                deals = [d for d in deals if d.get("id") != payload.get("id")]
                save_deals(deals)
                self._json({"ok": True})
            elif self.path == "/api/deals/create":
                try:
                    length = int(self.headers.get("Content-Length") or 0)
                    payload = json.loads(self.rfile.read(length).decode("utf-8"))
                except Exception:
                    self._json({"ok": False, "error": "Некорректный JSON"})
                    return
                deal = create_deal(payload.get("typeId"))
                if not deal:
                    self._json({"ok": False, "error": "Неизвестный тип сделки"})
                    return
                self._json({"ok": True, "deal": deal})
            elif self.path == "/api/deals/close":
                try:
                    length = int(self.headers.get("Content-Length") or 0)
                    payload = json.loads(self.rfile.read(length).decode("utf-8"))
                except Exception:
                    self._json({"ok": False, "error": "Некорректный JSON"})
                    return
                self._json(close_deal(payload.get("id")))
            elif self.path == "/api/deals/bind":
                try:
                    length = int(self.headers.get("Content-Length") or 0)
                    payload = json.loads(self.rfile.read(length).decode("utf-8"))
                except Exception:
                    self._json({"ok": False, "error": "Некорректный JSON"})
                    return
                self._json(bind_position(
                    payload.get("id"),
                    payload.get("src"),
                    isin=payload.get("isin"),
                    symbol=payload.get("symbol"),
                    login=payload.get("login"),
                    account=payload.get("account"),
                ))
            elif self.path == "/api/deals/unbind":
                try:
                    length = int(self.headers.get("Content-Length") or 0)
                    payload = json.loads(self.rfile.read(length).decode("utf-8"))
                except Exception:
                    self._json({"ok": False, "error": "Некорректный JSON"})
                    return
                self._json(unbind_position(
                    payload.get("id"),
                    payload.get("src"),
                    isin=payload.get("isin"),
                    symbol=payload.get("symbol"),
                ))
            elif self.path == "/api/deals/commission":
                try:
                    length = int(self.headers.get("Content-Length") or 0)
                    payload = json.loads(self.rfile.read(length).decode("utf-8"))
                except Exception:
                    self._json({"ok": False, "error": "Некорректный JSON"})
                    return
                self._json(deal_set_commission(payload.get("id"), payload.get("commission")))
            else:
                self.send_response(404)
                self.end_headers()
                self.wfile.write(b"404 Not Found")

    return Handler


LK_CACHE_FILE = os.path.join(BASE_DIR, ".lk_cache.json")


def preload_lk_cache():
    """Preload lk_state from cache file if it exists (fallback when MOEX API is unreachable)."""
    global lk_state
    if not os.path.exists(LK_CACHE_FILE):
        # also try legacy /tmp path
        for p in ("/tmp/lk.json", "/tmp/lk_fixed.json"):
            if os.path.exists(p):
                try:
                    with open(p, encoding="utf-8") as f:
                        raw = json.load(f)
                    _inject_lk_cache(raw)
                    print(f"[lk] загружены кэш-данные из {p}")
                    return
                except Exception:
                    pass
        return
    try:
        with open(LK_CACHE_FILE, encoding="utf-8") as f:
            raw = json.load(f)
        _inject_lk_cache(raw)
        print(f"[lk] загружены кэш-данные из {LK_CACHE_FILE}")
    except Exception as e:
        print(f"[lk] не удалось загрузить кэш: {e}")


def _inject_lk_cache(raw):
    """Inject raw lk API response data into lk_state."""
    global lk_state
    with lk_lock:
        current = {}
        for a in (raw.get("accounts") or []):
            login = a.get("login")
            if not login:
                continue
            current[login] = {
                "data": a.get("data") or {},
                "updated": a.get("updated"),
                "error": a.get("error"),
                "ts": time.time(),
            }
        lk_state["accounts"] = current


CT_CACHE_FILE = os.path.join(BASE_DIR, ".ct_cache.json")


def save_ct_cache():
    """Сохраняет последние данные cTrader в файл (переживает перезапуск/таймауты)."""
    with ct_lock:
        entries = [
            {"label": label, "data": st.get("data"), "updated": st.get("updated"), "error": st.get("error")}
            for label, st in ct_state["accounts"].items()
        ]
    try:
        with open(CT_CACHE_FILE, "w", encoding="utf-8") as f:
            json.dump({"entries": entries, "symbols": {str(k): v for k, v in ct_symbols_cache.items()}}, f, ensure_ascii=False)
    except Exception:
        pass


def preload_ct_cache():
    """Preload ct_state from cache file if it exists."""
    global ct_state
    cache_path = os.path.exists(CT_CACHE_FILE) and CT_CACHE_FILE
    if not cache_path:
        cache_path = os.path.exists("/tmp/ct.json") and "/tmp/ct.json"
    if not cache_path:
        return
    try:
        with open(cache_path, encoding="utf-8") as f:
            raw = json.load(f)
        current = {}
        for e in (raw.get("entries") or []):
            label = e.get("label", "XP BEE")
            current[label] = {
                "data": e.get("data"),
                "updated": e.get("updated"),
                "error": e.get("error"),
                "ts": time.time(),
            }
        with ct_lock:
            ct_state["accounts"] = current
        for k, v in (raw.get("symbols") or {}).items():
            try:
                ct_symbols_cache[int(k)] = v
            except Exception:
                pass
        ct_symbols_cache.update(CT_FALLBACK_SYMBOLS)
        print(f"[ct] загружены кэш-данные из {cache_path}")
    except Exception as ex:
        print(f"[ct] не удалось загрузить кэш: {ex}")


FUND_CACHE_FILE = os.path.join(BASE_DIR, ".fund_cache.json")


def preload_fund_cache():
    """Preload funding state from cache file if it exists."""
    global state
    if not os.path.exists(FUND_CACHE_FILE):
        return
    try:
        with open(FUND_CACHE_FILE, encoding="utf-8") as f:
            raw = json.load(f)
        with lock:
            state["data"] = raw.get("data")
            state["updated"] = raw.get("updated")
            state["error"] = raw.get("error")
            state["ts"] = time.time()
        print(f"[fund] загружены кэш-данные из {FUND_CACHE_FILE}")
    except Exception as e:
        print(f"[fund] не удалось загрузить кэш: {e}")


def run():
    from http.server import ThreadingHTTPServer
    preload_lk_cache()
    preload_ct_cache()
    preload_fund_cache()
    # авто-привязка открытых позиций к уже существующим пустым активным сделкам
    try:
        auto_bind_all()
    except Exception as e:
        print(f"[auto-bind] ошибка при стартовой привязке: {e}")
    server = ThreadingHTTPServer((HOST, PORT), make_handler())
    show_host = "localhost" if HOST in ("0.0.0.0", "::", "") else HOST
    clients = "все адреса" if "*" in ALLOWED_CLIENTS else ", ".join(sorted(ALLOWED_CLIENTS))
    print(f"Сервер запущен на http://{show_host}:{PORT} (доступ разрешён: {clients})")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    run()
