$ErrorActionPreference = 'Stop'
Set-Location $PSScriptRoot
$localBin = Join-Path $PSScriptRoot '.tools/lean-4.24.0-windows/bin'
if (Test-Path -LiteralPath $localBin) { $env:PATH = "$localBin;" + $env:PATH }
$env:PYTHONUTF8 = '1'
Write-Host 'Mathlib2 网页入口：http://127.0.0.1:8501 （DEMO.md 是说明文件）'
& "$PSScriptRoot/.venv/Scripts/python.exe" -m streamlit run app.py --server.address=127.0.0.1 --server.port=8501

