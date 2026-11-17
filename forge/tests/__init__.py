import atexit
import os
import shutil
import tempfile

# 测试里建的调度器不要把草稿写进真实的草稿目录（~/.rsi-math/scratch）；必须在导入 forge.leanrun 之前设好
if 'FORGE_SCRATCH' not in os.environ:
    _scratch = tempfile.mkdtemp(prefix='forge-test-scratch-')
    os.environ['FORGE_SCRATCH'] = _scratch
    atexit.register(shutil.rmtree, _scratch, True)

# 抄写检测默认会比本仓库所有 worktree 里的旧草稿；测试不应该读开发机上真实的 worktree。
# 把检出列表的缓存钉成只有当前检出（时间戳为无穷大，永不过期）；要测 checkouts() 本身的用例自己换掉缓存。
from forge import provenance as _provenance  # noqa: E402
_provenance._checkouts[:] = [float('inf'), [_provenance.ROOT]]
