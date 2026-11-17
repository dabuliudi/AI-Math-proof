import atexit
import os
import shutil
import tempfile

# 测试里建的调度器不要把草稿写进真实的草稿目录（~/.rsi-math/scratch）；必须在导入 forge.leanrun 之前设好
if 'FORGE_SCRATCH' not in os.environ:
    _scratch = tempfile.mkdtemp(prefix='forge-test-scratch-')
    os.environ['FORGE_SCRATCH'] = _scratch
    atexit.register(shutil.rmtree, _scratch, True)
