@echo off
chcp 65001 >nul
title LUIGI IPTV PLAYLIST MAKER 0.2.0 - TVORBA EXE
cd /d "%~dp0"
where py >nul 2>nul
if errorlevel 1 (
 echo CHYBA: Python nebyl nalezen.
 pause
 exit /b 1
)
py -m pip install -r requirements.txt
if errorlevel 1 pause & exit /b 1
py -m PyInstaller --noconfirm --clean --onefile --windowed --distpath "dist" --workpath "build" --specpath "build" --name "LUIGI IPTV PLAYLIST MAKER" "src\luigi_iptv_playlist_maker.py"
if errorlevel 1 pause & exit /b 1
echo HOTOVO: "%~dp0dist\LUIGI IPTV PLAYLIST MAKER.exe"
pause
