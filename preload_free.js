const { contextBridge, ipcRenderer } = require('electron');

contextBridge.exposeInMainWorld('electronAPI', {
  onUpdateMarkers: (callback) => ipcRenderer.on('update-markers', callback),
  onUpdateClips: (callback) => ipcRenderer.on('update-clips', callback)
});
