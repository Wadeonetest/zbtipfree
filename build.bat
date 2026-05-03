@echo off
chcp 65001 > nul
echo ========================================
echo 直播录屏标记助手 - 打包脚本
echo ========================================
echo.

echo [1/4] 检查 PyInstaller 是否已安装...
pip show pyinstaller > nul 2>&1
if %errorlevel% neq 0 (
    echo 正在安装 PyInstaller...
    pip install pyinstaller
) else (
    echo PyInstaller 已安装
)

echo.
echo [2/4] 开始打包...
echo.

pyinstaller --onefile ^
    --windowed ^
    --name "直播录屏标记助手" ^
    --icon=NONE ^
    --add-data "使用教程_free.md;." ^
    --add-data "运行教程_free.md;." ^
    screen_recorder_free.py

if %errorlevel% equ 0 (
    echo.
    echo [3/4] 打包成功！
    echo.
    echo [4/4] 清理临时文件...
    rmdir /s /q build
    del /q "直播录屏标记助手.spec"
    echo.
    echo ========================================
    echo 打包完成！
    echo 可执行文件位置：dist\直播录屏标记助手.exe
    echo ========================================
) else (
    echo.
    echo 打包失败，请检查错误信息
)

pause
