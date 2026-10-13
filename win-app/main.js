const { app, BrowserWindow, ipcMain } = require('electron');
const path = require('path');

const SERVER_URL = process.env.MOEX_URL || 'http://127.0.0.1:8642';

let win = null;

function createWindow() {
  win = new BrowserWindow({
    width: 380,
    height: 620,
    minWidth: 320,
    minHeight: 420,
    frame: false,
    useContentSize: true,
    alwaysOnTop: true,
    fullscreenable: false,
    backgroundColor: '#0d1117',
    title: 'MOEX Mini',
    icon: path.join(__dirname, 'favicon.png'),
    webPreferences: {
      preload: path.join(__dirname, 'preload.js'),
      contextIsolation: true,
      nodeIntegration: false,
      enableRemoteModule: false
    }
  });

  win.setMenuBarVisibility(false);
  win.loadURL(SERVER_URL);

  win.webContents.on('did-finish-load', () => {
    win.webContents.insertCSS(require('fs').readFileSync(path.join(__dirname, 'styles.css'), 'utf8'));
    win.webContents.executeJavaScript(`
      +function() {
        var dealsTab = document.querySelector('.tabs .tab[data-tab="deals"]');
        if (dealsTab) dealsTab.remove();
        var dealsPane = document.querySelector('.tabpane[data-pane="deals"]');
        if (dealsPane) dealsPane.remove();

        var bar = document.createElement('div');
        bar.id = 'mini-bar';
        bar.innerHTML =
          '<div class="mini-title">MOEX Mini</div>' +
          '<button class="mb pin" title="Поверх всех окон">\u2606</button>' +
          '<button class="mb" title="Свернуть" data-act="hide">\u2013</button>' +
          '<button class="mb quit" title="Закрыть" data-act="quit">\u2715</button>';
        var body = document.body;
        body.insertBefore(bar, body.firstChild);

        var pinned = true;
        var pinBtn = bar.querySelector('.pin');
        function syncPin() {
          pinBtn.textContent = pinned ? '\u2605' : '\u2606';
          pinBtn.classList.toggle('pinned', pinned);
        }
        pinBtn.addEventListener('click', function() {
          pinned = !pinned;
          window.mini.pin(pinned);
          syncPin();
        });
        bar.addEventListener('click', function(e) {
          var act = e.target.getAttribute && e.target.getAttribute('data-act');
          if (act === 'hide') window.mini.hide();
          if (act === 'quit') window.mini.quit();
        });
        syncPin();

        if (window.mini && typeof window.mini.onReady === 'function') window.mini.onReady();
      };
    `).catch(function(){});
  });

  win.webContents.on('did-fail-load', (e, code, desc) => {
    if (win) win.webContents.executeJavaScript(
      'document.body.innerHTML = "<div style=\\"padding:20px;color:#8b949e;font:14px system-ui;\\">Нет связи с сервером (" + ' +
      JSON.stringify(SERVER_URL.split('//')[1]) + ' + ").<br><br>Запустите moex-web на сервере и нажмите Обновить.</div>";'
    );
  });
}

app.whenReady().then(() => {
  createWindow();
  app.on('activate', () => {
    if (BrowserWindow.getAllWindows().length === 0) createWindow();
  });
});

app.on('window-all-closed', () => {
  if (process.platform !== 'darwin') app.quit();
});

ipcMain.on('mini:pin', (e, on) => {
  if (win) win.setAlwaysOnTop(!!on);
});

ipcMain.on('mini:hide', (e) => {
  if (win) win.hide();
});

ipcMain.on('mini:quit', (e) => {
  app.quit();
});