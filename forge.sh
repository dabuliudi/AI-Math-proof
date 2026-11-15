#!/bin/sh
# forge 命令行入口（macOS / Linux）：./forge.sh status
cd "$(dirname "$0")" || exit 1
export PYTHONUTF8=1
[ -d "$HOME/.elan/bin" ] && export PATH="$HOME/.elan/bin:$PATH"
PY=.venv/bin/python; [ -x "$PY" ] || PY=python3
exec "$PY" -m forge "$@"
