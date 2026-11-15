"""论文入口：复用仓库已有的规则提取（mathlib2.ingest），产出待形式化的命题清单。

提取只负责“原文里有哪些命题、在第几页”；把自然语言译成 Lean 命题由 agent 完成，
译得对不对由另一个 agent 独立复核（review），最终是否采信由人决定。Lean 只能保证证明对，不能保证命题译对了。
"""
import json
import time

from .leanrun import DATA

PAPERS = DATA / 'papers'
REVIEWS = DATA / 'reviews.jsonl'
KINDS = {'theorem', 'lemma', 'proposition', 'corollary', 'conjecture'}


def extract(path):
    from mathlib2.ingest import ingest
    document = ingest(str(path))
    items = []
    for obj in document['objects']:
        if str(obj.get('object_type', '')).lower() not in KINDS:
            continue
        items.append(dict(id=f'{document["sha256"][:8]}:{len(items) + 1}', kind=obj['object_type'].lower(),
                          title=obj.get('title', ''), page=obj.get('page'),
                          text=(obj.get('statement_text') or obj.get('text') or '').strip(),
                          has_proof=bool(obj.get('proof_body')), confidence=obj.get('confidence')))
    worklist = dict(file=document['filename'], sha256=document['sha256'], pages=len(document['pages']),
                    method=document.get('method', ''), statements=items,
                    note='规则提取可能漏掉或截断命题；页码是 PDF 页序。形式化时以原文为准。')
    PAPERS.mkdir(parents=True, exist_ok=True)
    (PAPERS / f'{document["sha256"][:8]}.json').write_text(json.dumps(worklist, ensure_ascii=False, indent=2), encoding='utf-8')
    return worklist


def review(name, agent, verdict, note):
    """独立复核 Lean 命题与原文是否一致。追加记录，不覆盖；同一命题可以有多份复核。"""
    record = dict(task=name, agent=agent, verdict=verdict, note=note[:3000], at=time.strftime('%Y-%m-%dT%H:%M:%S%z'))
    DATA.mkdir(parents=True, exist_ok=True)
    with open(REVIEWS, 'a', encoding='utf-8') as handle:
        handle.write(json.dumps(record, ensure_ascii=False) + '\n')
    return dict(ok=True, record=record)


def reviews():
    if not REVIEWS.exists():
        return {}
    out = {}
    for line in REVIEWS.read_text(encoding='utf-8').splitlines():
        if line.strip():
            record = json.loads(line)
            out.setdefault(record['task'], []).append(record)
    return out
