"""真实Lean声明目录；缓存的是通用类型，不含目标答案。"""
import json
import re
import hashlib
from pathlib import Path
from .compiler import ROOT
from .evidence import digest


def load_rules(compiler):
    extractor=ROOT/'phase2/Extract.lean'
    cache=ROOT/'phase2/library.json'
    key=digest(extractor.read_text(encoding='utf-8')+(ROOT/'lean/lake-manifest.json').read_text())
    # 目录里记录的是本机绝对路径，换机器后失效；本机重新抽取的结果写到不入库的 library.local.json，不改动入库文件。
    local=ROOT/'phase2/library.local.json'
    for cache in (local,cache):
        if not cache.exists(): continue
        data=json.loads(cache.read_text(encoding='utf-8'))
        if data.get('key')==key and all(Path(p).exists() and hashlib.sha256(Path(p).read_bytes()).hexdigest()==h for p,h in data['source_hashes'].items()):
            compiler.journal.event('retrieval',mode='cached_real_lean_types',key=key,count=len(data['rules']))
            return data['rules']
    result=compiler.execute(extractor,timeout=180)
    compiler.journal.save('retrieval-compile.json',result)
    if result['returncode']!=0:
        raise RuntimeError('真实Lean规则检索失败，查看retrieval-compile.json')
    rules=[]; hashes={}; core=compiler.lean_src()
    for line in result['stdout'].splitlines():
        if not line.startswith('P2_RULE '): continue
        entry=json.loads(line[len('P2_RULE '):]); rule=entry['rule']
        if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_.\x27]*',rule['name']): continue
        module=entry['module']; base=ROOT/'lean/.lake/packages/mathlib' if module.startswith('Mathlib.') else core
        path=base/(module.replace('.','/')+'.lean')
        if not path.is_file(): continue
        hashes[str(path)]=hashlib.sha256(path.read_bytes()).hexdigest()
        rule.update(module=module,path=str(path),line=entry['line'],source_sha256=hashes[str(path)],origin='Mathlib Reuse' if module.startswith('Mathlib.') else 'Lean Core Reuse')
        rules.append(rule)
    rules.sort(key=lambda r:r['name'])
    local.write_text(json.dumps(dict(key=key,rules=rules,source_hashes=hashes),ensure_ascii=False,indent=2),encoding='utf-8')
    compiler.journal.event('retrieval',mode='live_lean_type_decoder',count=len(rules),key=key)
    return rules


def rank_rules(rules,goals):
    ops={g.op for g in goals}
    return sorted(rules,key=lambda r:(-(4*(r['conclusion']['op'] in ops)+sum(p['op'] in ops for p in r['premises'])),len(r['premises']),r['name']))
