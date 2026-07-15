@echo off
chcp 65001 >nul
title LUIGI IPTV PLAYLIST MAKER 0.2.0 - TEST
cd /d "%~dp0"
where py >nul 2>nul
if errorlevel 1 (
 echo CHYBA: Python nebyl nalezen.
 pause
 exit /b 1
)
py "src\luigi_iptv_playlist_maker.py"
if errorlevel 1 pause
