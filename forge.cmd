@echo off
rem Forge command-line entry for Windows: forge.cmd status
setlocal
cd /d "%~dp0"
set PYTHONUTF8=1
if exist "%USERPROFILE%\.elan\bin" set "PATH=%USERPROFILE%\.elan\bin;%PATH%"
set "PY=.venv\Scripts\python.exe"
if not exist "%PY%" set "PY=python"
"%PY%" -m forge %*
