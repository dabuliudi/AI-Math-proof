@echo off
cd /d "%~dp0"
set PYTHONUTF8=1
set "PATH=%~dp0.tools\lean-4.24.0-windows\bin;%PATH%"
if not exist ".venv\Scripts\python.exe" (
  echo Python environment missing. Please follow README setup steps.
  pause
  exit /b 1
)
".venv\Scripts\python.exe" -m streamlit run app.py --server.address=127.0.0.1 --server.port=8501
if errorlevel 1 pause
