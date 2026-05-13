# -*- mode: python ; coding: utf-8 -*-

from PyInstaller.utils.hooks import collect_dynamic_libs, collect_data_files

# 收集 numpy 的动态库文件
numpy_binaries = collect_dynamic_libs('numpy')
cv2_binaries = collect_dynamic_libs('cv2')

# 收集 numpy 的数据文件和 Python 文件
numpy_datas = collect_data_files('numpy', include_py_files=True, subdir='.')
# 过滤掉测试文件
numpy_datas = [(src, dst) for src, dst in numpy_datas if 'test' not in src.lower() and 'tests' not in src.lower()]

cv2_datas = collect_data_files('cv2', include_py_files=True)


a = Analysis(
    ['live_recorder_sprite.py'],
    pathex=[],
    binaries=[*numpy_binaries, *cv2_binaries],
    datas=[('app_icon.ico', '.'), *numpy_datas, *cv2_datas],
    hiddenimports=[
        'mss',
        'pyaudiowpatch',
        'pygame',
        'pygame.mixer',
        'pygame.base',
        'wave',
        'numpy',
        'numpy._core',
        'numpy._core.multiarray',
        'numpy._core.umath',
        'numpy._core._simd',
        'cv2',
        'cv2.data',
        'PIL',
        'PIL.Image',
        'PIL.ImageTk',
        'requests',
        'watchdog',
        'watchdog.observers',
        'watchdog.events',
        'imageio_ffmpeg',
        'pyautogui',
    ],
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    excludes=['matplotlib', 'numpy.tests', 'numpy.ma.tests', 'numpy.matrixlib.tests', 'numpy.random.tests', 'numpy.polynomial.tests', 'numpy.linalg.tests'],
    noarchive=False,
)
pyz = PYZ(a.pure)

exe = EXE(
    pyz,
    a.scripts,
    a.binaries,
    a.datas,
    [],
    name='直播录屏标记精灵',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=True,
    upx_exclude=[],
    runtime_tmpdir=None,
    console=False,
    disable_windowed_traceback=False,
    argv_emulation=False,
    target_arch=None,
    codesign_identity=None,
    entitlements_file=None,
    icon='app_icon.ico',
)
