param(
    [ValidateSet('responses','chat_completions')][string]$Provider = 'chat_completions',
    [ValidateSet('json_schema','json_object','prompt_json')][string]$OutputMode = 'json_schema',
    [ValidateSet('max_tokens','max_completion_tokens')][string]$ChatTokenField = 'max_completion_tokens'
)
$ErrorActionPreference = 'Stop'
$repoRoot = Split-Path -Parent $PSScriptRoot
$pythonPath = Join-Path $repoRoot '.venv\Scripts\python.exe'
$previousLocation = Get-Location
$names = @('PROVIDER','BASE_URL','MODEL','API_KEY','INPUT_USD_PER_MILLION','OUTPUT_USD_PER_MILLION','PRICE_SOURCE','PRICE_AS_OF','OUTPUT_MODE','CHAT_TOKEN_FIELD','MAX_ATTEMPTS','MAX_COST_USD')
$previousValues = @{}
foreach ($name in $names) { $previousValues[$name] = [Environment]::GetEnvironmentVariable("MATHLIB2_GW_$name",'Process') }
$previousUtf8 = $env:PYTHONUTF8
$secureKey = $null
$keyPointer = [IntPtr]::Zero
$resultCode = 2
try {
    Set-Location -LiteralPath $repoRoot
    $env:PYTHONUTF8 = '1'
    $env:MATHLIB2_GW_PROVIDER = $Provider
    $env:MATHLIB2_GW_OUTPUT_MODE = $OutputMode
    $env:MATHLIB2_GW_CHAT_TOKEN_FIELD = $ChatTokenField
    $env:MATHLIB2_GW_BASE_URL = Read-Host 'API根地址（例如 https://api.openai.com/v1）'
    $env:MATHLIB2_GW_MODEL = Read-Host '服务商提供的模型名称'
    $secureKey = Read-Host 'API密钥（隐藏输入，请勿发送到聊天）' -AsSecureString
    $keyPointer = [Runtime.InteropServices.Marshal]::SecureStringToBSTR($secureKey)
    $env:MATHLIB2_GW_API_KEY = [Runtime.InteropServices.Marshal]::PtrToStringBSTR($keyPointer)
    $env:MATHLIB2_GW_INPUT_USD_PER_MILLION = Read-Host '每百万输入Token的美元价格（以服务商报价为准）'
    $env:MATHLIB2_GW_OUTPUT_USD_PER_MILLION = Read-Host '每百万输出Token的美元价格（以服务商报价为准）'
    $env:MATHLIB2_GW_PRICE_SOURCE = Read-Host '价格来源网页或账单文档引用'
    $env:MATHLIB2_GW_PRICE_AS_OF = Read-Host '价格适用日期（YYYY-MM-DD）'
    $env:MATHLIB2_GW_MAX_ATTEMPTS = '1'
    $env:MATHLIB2_GW_MAX_COST_USD = '0.10'
    & $pythonPath -B -m mathlib2_gateway
    $resultCode = $LASTEXITCODE
} finally {
    if ($keyPointer -ne [IntPtr]::Zero) { [Runtime.InteropServices.Marshal]::ZeroFreeBSTR($keyPointer) }
    if ($null -ne $secureKey) { $secureKey.Dispose() }
    foreach ($name in $names) { [Environment]::SetEnvironmentVariable("MATHLIB2_GW_$name",$previousValues[$name],'Process') }
    $env:PYTHONUTF8 = $previousUtf8
    Set-Location -LiteralPath $previousLocation.Path
}
exit $resultCode
