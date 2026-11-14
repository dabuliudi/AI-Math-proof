"""在逐字节副本运行旧版三项实验测试；只把真实编译的依赖目录指向原Lean工程。"""
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time
import unittest
import uuid
from pathlib import Path
from unittest.mock import patch

root = Path(__file__).resolve().parents[2]
out = root / 'phase2' / 'legacy-regression' / uuid.uuid4().hex
workspace = out / 'workspace'
baseline = root / 'audits/lemma3-v031-80ab8af1/workspace'
copied = {}
for old in baseline.rglob('*'):
    if not old.is_file() or '__pycache__' in old.parts:
        continue
    relative = old.relative_to(baseline)
    source = root / relative
    if not source.is_file():
        continue
    dest = workspace / relative
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, dest)
    assert dest.read_bytes() == source.read_bytes()
    copied[str(relative)] = hashlib.sha256(source.read_bytes()).hexdigest()
os.chdir(workspace)
sys.path.insert(0, str(workspace))
os.environ['MATHLIB2_INTEGRATION'] = '1'
os.environ['MATHLIB2_LAKE'] = str(root / '.tools/lean-4.24.0-windows/bin/lake.exe')
real_popen = subprocess.Popen
calls = []
def live_popen(command, *args, **kwargs):
    if Path(kwargs.get('cwd', '.')).resolve() == workspace / 'lean':
        kwargs['cwd'] = root / 'lean'
    calls.append(dict(command=command, cwd=str(kwargs.get('cwd', workspace))))
    return real_popen(command, *args, **kwargs)

suite = unittest.TestSuite()
for name in ('test_alignment.py', 'test_formalization.py', 'test_lemma2.py', 'test_lemma3.py'):
    suite.addTests(unittest.defaultTestLoader.discover(str(workspace / 'tests'), pattern=name))
start = time.perf_counter()
with (out / 'tests.txt').open('w', encoding='utf-8') as stream, patch('subprocess.Popen', live_popen):
    result = unittest.TextTestRunner(stream=stream, verbosity=2).run(suite)
summary = dict(tests=result.testsRun, failures=len(result.failures), errors=len(result.errors),
               skipped=len(result.skipped), success=result.wasSuccessful(), elapsed=time.perf_counter()-start,
               workspace=str(workspace), copied_source_hashes=copied, real_subprocess_calls=calls)
(out / 'result.json').write_text(json.dumps(summary, ensure_ascii=False, indent=2), encoding='utf-8')
print(json.dumps({k:v for k,v in summary.items() if k not in ('copied_source_hashes','real_subprocess_calls')}, ensure_ascii=False))
sys.exit(0 if result.wasSuccessful() else 1)
