"""真实多项式实验：受信任可复跑模板，逐项标明原始生成来源，无任意代码执行入口。"""
import hashlib
import json
import os
import shutil
import subprocess
import time
import uuid
from pathlib import Path
from .lean import accepted
from .toolchain import find_lake, kill_tree

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / 'lean'
SOURCE = '''import Mathlib.RingTheory.Polynomial.Radical
open Polynomial UniqueFactorizationMonoid EuclideanDomain
theorem mathlib2_mason_lemma1 {k : Type*} [Field k] [DecidableEq k]
    (a : k[X]) (_ha : a ≠ 0) :
    a / radical a ∣ derivative a := by
  classical
  simpa only [divRadical] using (divRadical_dvd_derivative a)
#print axioms mathlib2_mason_lemma1
'''


def templates():
    result = {'mason_lemma1': dict(label='Mason–Stothers Lemma 1：复用 Mathlib',
        source=SOURCE, target='∀ {k : Type*} [Field k] [DecidableEq k] (a : k[X]), a ≠ 0 → a / radical a ∣ derivative a',
        name='mathlib2_mason_lemma1', scope='target',
        source_match=r'(?is)\bLemma\s*1\b.*?nonzero\s*polynomial\s*a.*?rad\s*\(\s*a\s*\).*?divides\s*a',
        provenance=dict(category='Theorem Reuse', new_statement=True, new_proof=False,
            authors='Jineon Baek, Seewoo Lee（论文及 Mathlib 原证明作者）',
            declaration='divRadical_dvd_derivative',
            file='Mathlib/RingTheory/Polynomial/Radical.lean', line=31,
            definitions_file='Mathlib/RingTheory/Radical.lean',
            paper='2408.15180v2.pdf', paper_pages=[2,4,6,8],
            assumptions=['Field k（任意特征）','DecidableEq k（定义所需实例，可由经典逻辑提供）','a : Polynomial k','a ≠ 0（保留论文假设；复用定理更强）'],
            alignment='radical 为不计重数的首一不可约因子乘积；除法是多项式欧几里得除法，divRadical 定义展开。',
            note='模板由开发者明确构造，无 AI API 调用；复用已发表证明，不是独立新证明。'))}
    from .lemma2 import template
    result['mason_lemma2']=template(SOURCE)
    from .lemma3 import template as lemma3_template
    result['mason_lemma3']=lemma3_template()
    return result


def check_template(template_id, timeout=120):
    if template_id not in templates():
        raise ValueError('未知或不受信任的 Lean 模板；不执行任意代码')
    if not 1 <= timeout <= 300:
        raise ValueError('编译超时须在1至300秒内')
    template = templates()[template_id]
    run_id = uuid.uuid4().hex
    folder = PROJECT/'Research'
    folder.mkdir(exist_ok=True)
    artifact = folder/f'Attempt_{run_id}.lean'
    artifact.write_text(template['source'],encoding='utf-8')
    result = dict(template,template_id=template_id,attempt_id=run_id,accepted=False,status='not_run',
                  stdout='',stderr='',returncode=None,axioms=[],artifact=str(artifact),
                  sha256=hashlib.sha256(template['source'].encode()).hexdigest(),elapsed=0,
                  toolchain=(PROJECT/'lean-toolchain').read_text().strip(),reason='')
    result['reused_declarations'] = template.get('reused_declarations',[{'name':'divRadical_dvd_derivative',
        'path':'Mathlib/RingTheory/Polynomial/Radical.lean','line':31}])
    lake = find_lake()
    started = time.monotonic()
    manifest=PROJECT/'lake-manifest.json'
    if manifest.exists():
        result['manifest_sha256']=hashlib.sha256(manifest.read_bytes()).hexdigest()
    if not lake:
        result['reason']='Lean/Lake未安装；请安装固定工具链后重试'
    else:
        command=[lake,'env','lean','-M','2048',str(artifact)]
        result['command']=command
        env=os.environ.copy()
        env['PATH']=str(Path(lake).parent)+os.pathsep+env.get('PATH','')
        phase='toolchain_version'
        try:
            version=subprocess.run([lake,'env','lean','--version'],cwd=PROJECT,env=env,capture_output=True,text=True,encoding='utf-8',timeout=min(timeout,60))
            result['lean_version']=version.stdout.strip()
            phase='compile'
            proc=subprocess.Popen(command,cwd=PROJECT,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,
                                  text=True,encoding='utf-8',errors='replace',start_new_session=os.name!='nt')
            try:
                result['stdout'],result['stderr']=proc.communicate(timeout=timeout)
            except subprocess.TimeoutExpired:
                if os.name=='nt':
                    subprocess.run(['taskkill','/PID',str(proc.pid),'/T','/F'],capture_output=True)
                else:
                    import signal
                    os.killpg(proc.pid,signal.SIGKILL)
                proc.kill()
                result['stdout'],result['stderr']=proc.communicate()
                raise
            result['returncode']=proc.returncode
            ok,axioms=accepted(result['stdout']+result['stderr'],template['name'],proc.returncode)
            result['declaration_audits']={}
            for name in template.get('audit_names',[template['name']]):
                audited, used = accepted(result['stdout']+result['stderr'],name,proc.returncode)
                result['declaration_audits'][name]={'accepted':audited,'axioms':used}
                ok=ok and audited
            result.update(accepted=ok,axioms=axioms,status='verified' if ok else 'failed',
                          reason='真实 Lean 编译及公理审计通过（'+template['provenance']['category']+'）' if ok else '编译或公理审计失败；查看原始输出并补齐依赖后重试')
        except subprocess.TimeoutExpired:
            result.update(status='timeout',timeout_phase=phase,
                          reason=('工具链版本查询超时，尚未开始证明编译；检查本地工具链并重试' if phase=='toolchain_version'
                                  else '编译超时；结果未知，可补齐缓存后重试'))
        except OSError as exc:
            result.update(status='failed',reason=str(exc))
    result['elapsed']=time.monotonic()-started
    prefix={'mason_lemma2':'lemma2','mason_lemma3':'lemma3'}.get(template_id,'lemma1-v03')
    report=ROOT/'reports'/f'{prefix}-{run_id}.json'
    report.parent.mkdir(exist_ok=True)
    result['log_artifact']=str(report)
    report.write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf-8')
    return result
