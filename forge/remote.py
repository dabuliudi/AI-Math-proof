"""按内容检索 Mathlib：直接复用社区已有的检索服务，不自己建索引。

- LeanSearch（https://leansearch.net）：自然语言 / 命题文本的语义检索；
- Loogle（https://loogle.lean-lang.org）：按类型模式检索。

两者就是 Mathlib 自带的 LeanSearchClient 调用的同一批接口。它们索引的是较新的 Mathlib，
名称可能与本工程固定的版本略有出入，用之前拿 `forge lookup` 核对一下。发出去的只有检索词本身。
"""
import json
import urllib.error
import urllib.parse
import urllib.request

AGENT = 'lean-search-client'
LEANSEARCH = 'https://leansearch.net/search'
LOOGLE = 'https://loogle.lean-lang.org/json'


def _fetch(request, timeout):
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            return json.loads(response.read().decode('utf-8')), None
    except (urllib.error.URLError, TimeoutError, ValueError, OSError) as exc:
        return None, f'检索服务不可用：{exc}'


def leansearch(query, limit=8, timeout=30):
    body = json.dumps({'query': [query], 'num_results': limit}).encode('utf-8')
    request = urllib.request.Request(LEANSEARCH, data=body, method='POST', headers={
        'accept': 'application/json', 'Content-Type': 'application/json', 'User-Agent': AGENT})
    data, error = _fetch(request, timeout)
    if error:
        return dict(ok=False, reason=error)
    results = []
    for item in (data[0] if data else [])[:limit]:
        result = item.get('result', {})
        entry = '.'.join(result.get('name', [])) + ' : ' + (result.get('type') or '')
        description = result.get('informal_description') or result.get('docstring') or ''
        results.append(dict(theorem=entry[:1200], kind=result.get('kind', ''), about=description[:300]))
    return dict(ok=True, source='LeanSearch', results=results,
                note='语义检索，索引的是较新的 Mathlib；用 lookup 核对名称在本工程里是否存在')


def loogle(pattern, limit=12, timeout=30):
    request = urllib.request.Request(LOOGLE + '?q=' + urllib.parse.quote(pattern), headers={'User-Agent': AGENT})
    data, error = _fetch(request, timeout)
    if error:
        return dict(ok=False, reason=error)
    if data.get('error'):
        return dict(ok=False, reason=data['error'], suggestions=data.get('suggestions', []))
    hits = [f'{h.get("name", "")} : {h.get("type", "")}'[:1200] for h in data.get('hits', [])[:limit]]
    return dict(ok=True, source='Loogle', header=data.get('header', '').strip(), results=hits,
                suggestions=data.get('suggestions', []))
