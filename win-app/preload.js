const { contextBridge, ipcRenderer } = require('electron');

contextBridge.exposeInMainWorld('mini', {
  onReady: () => {},
  pin: (on) => ipcRenderer.send('mini:pin', on),
  hide: () => ipcRenderer.send('mini:hide'),
  quit: () => ipcRenderer.send('mini:quit')
});