#!/bin/sh
# macOS / Linux 启动入口；Windows 请用 run-demo.cmd。
cd "$(dirname "$0")" || exit 1
export PYTHONUTF8=1
[ -d "$HOME/.elan/bin" ] && export PATH="$HOME/.elan/bin:$PATH"
if [ ! -x .venv/bin/python ]; then
  echo "缺少 Python 环境：先执行 python3.11+ -m venv .venv && .venv/bin/pip install -e '.[pdf]'" >&2
  exit 1
fi
echo "Mathlib2 网页入口：http://127.0.0.1:${PORT:-8501}"
exec .venv/bin/python -m streamlit run app.py --server.address=127.0.0.1 --server.port="${PORT:-8501}" --server.headless=true
