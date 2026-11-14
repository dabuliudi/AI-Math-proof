"""本地源码词法检索。结果不是可用性证明，最终仍须 Lean 检查。"""
import re
from itertools import islice
from pathlib import Path
from functools import lru_cache


def search(query, root, limit=8):
    tokens = set(re.findall(r'[A-Za-z_][A-Za-z_0-9]*', query.lower()))
    results = []
    # 有界演示：扫描前 200 个文件，不冒充全库索引。
    for path in islice(Path(root).rglob('*.lean'), 200):
        for number, line in enumerate(path.read_text(encoding='utf-8', errors='replace').splitlines(), 1):
            if re.search(r'\b(theorem|lemma|def)\s+', line):
                score = sum(t in line.lower() for t in tokens)
                if score:
                    results.append({'path': str(path.resolve()), 'line': number, 'text': line.strip(), 'score': score})
    return sorted(results, key=lambda r: -r['score'])[:limit]


def knowledge_search(store, query):
    approved = {r['candidate_id'] for r in store.rows('verified')}
    return [r for r in store.rows('candidates') if r['id'] in approved and query.lower() in r['payload']['statement'].lower()]


def _tokens(text):
    # 拆开 Lean camelCase，并映射少量数学记号；不声称语义等价。
    text = re.sub(r'([a-z])([A-Z])',r'\1 \2',text)
    for symbol,word in {'∣':' divisibility dvd ',"'":' derivative ','≤':' le ','≠':' ne ','[X]':' polynomial '}.items():
        text = text.replace(symbol,word)
    words = set(re.findall(r'[A-Za-z][A-Za-z0-9]*',text.lower()))
    synonyms = {'divides':'dvd','divisibility':'dvd','rad':'radical','coprime':'coprime','characteristic':'char'}
    return words | {synonyms[w] for w in words if w in synonyms}


@lru_cache(maxsize=3)
def declaration_index(root):
    """全目录声明索引；命名空间为源码语法推断，非 Lean elaboration。"""
    entries=[]
    for path in sorted(Path(root).rglob('*.lean')):
        raw=path.read_text(encoding='utf-8',errors='replace')
        clean=re.sub(r'/\-.*?\-/',lambda m:'\n'*m.group().count('\n'),raw,flags=re.S)
        lines=clean.splitlines()
        namespaces=[]
        for i,line in enumerate(lines):
            stripped=line.split('--')[0].strip()
            ns=re.match(r'namespace\s+(\S+)',stripped)
            if ns:
                namespaces.append(ns[1])
            end=re.match(r'end(?:\s+(\S+))?$',stripped)
            if end and namespaces and end[1]==namespaces[-1]:
                namespaces.pop()
            m=re.match(r'(?:@\[.*?\]\s*)?(?:protected\s+|noncomputable\s+|private\s+)*(theorem|lemma|def|abbrev)\s+([\w.\u0080-\uffff]+)',stripped)
            if not m:
                continue
            declaration='\n'.join(lines[i:i+30]).split(':=')[0].split(' where')[0].strip()
            # 无 := 的特殊声明只展示首行，避免把后面的声明误接进来。
            if len(declaration)>3000 or re.search(r'\n(?:theorem|lemma|def) ',declaration):
                declaration=stripped
            namespace='.'.join(namespaces)
            name=m[2] if '.' in m[2] or not namespace else namespace+'.'+m[2]
            entry=dict(name=name,namespace=namespace or '(root)',namespace_method='source_syntax',
                declaration=declaration,path=str(path.resolve()),line=i+1,text=stripped,
                module='Mathlib.'+'.'.join(path.relative_to(root).with_suffix('').parts),
                context='\n'.join(lines[max(0,i-12):i]),kind=m[1])
            entry['_tokens']=_tokens(declaration+' '+str(path.relative_to(root)))
            entries.append(entry)
    return entries


def search_mathlib(query, root=None, limit=12):
    root=Path(root or Path(__file__).resolve().parents[1]/'lean/.lake/packages/mathlib/Mathlib')
    if not root.exists():
        raise FileNotFoundError('本地 Mathlib 源码未安装；先完成 README 的 Lean 初始化')
    tokens=_tokens(query)
    if not tokens:
        return []
    results=[]
    for item in declaration_index(str(root.resolve())):
        overlap=tokens & item['_tokens']
        if not overlap:
            continue
        exact=query.strip() in {item['name'],item['name'].split('.')[-1]}
        signature_overlap=tokens & _tokens(item['declaration'])
        score=100 if exact else len(overlap)+2*len(signature_overlap)
        result={k:v for k,v in item.items() if k!='_tokens'}
        result.update(score=score,matched_tokens=sorted(overlap),
            match_kind='exact_identifier' if exact else ('partial_expression' if len(signature_overlap)>=2 else 'keyword_only'),
            equivalence='not_established',reuse_status='requires_lean_check',
            suggestion='可尝试复用此声明；核对变量/类型类/假设后用Lean验证，尚不能断言与论文等价')
        results.append(result)
    return sorted(results,key=lambda x:(-x['score'],x['name']))[:limit]
