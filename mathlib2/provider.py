"""提供者只输出受限命题和策略编号，不能输出任意可执行 Lean 命令。"""
import json
import os
import urllib.request

SAMPLES = [
    {'statement': '∀ n : Nat, n + 0 = n', 'strategy': 'omega', 'neg_strategy': 'at_zero', 'label': '加零不变'},
    {'statement': '∀ n : Nat, (n + 0) + 0 = n', 'strategy': 'reuse', 'neg_strategy': 'at_zero', 'label': '两次加零'},
    {'statement': '∀ n : Nat, n + 1 = n', 'strategy': 'omega', 'neg_strategy': 'at_zero', 'label': '错误猜想'},
    {'statement': '∀ n : Nat, n * n = n', 'strategy': 'omega', 'neg_strategy': 'at_zero', 'label': '有限策略未解决'},
]


class MockProvider:
    name = 'mock（固定样例，无 AI 调用）'

    def generate(self, source, limit):
        # 只对明确标记的教学样例建立映射，绝不把任意论文套用为样例证明。
        if 'MATHLIB2_DEMO_NAT' not in source:
            return []
        return [dict(s) for s in SAMPLES[:limit]]


class HTTPProvider:
    name = 'http（外部 JSON 服务）'

    def generate(self, source, limit):
        url = os.environ.get('MATHLIB2_API_URL', '')
        if not url.startswith(('https://', 'http://localhost:', 'http://127.0.0.1:')):
            raise ValueError('请配置 HTTPS API 地址，或本地 HTTP 服务')
        key = os.environ.get('MATHLIB2_API_KEY', '')
        payload = {'task': '将来源中的命题或其邻近猜想转为受限自然数 Lean 命题。返回 candidates 数组，每项含 statement、strategy、neg_strategy、label。strategy 取 omega/simp；neg_strategy 取 at_zero。不要声称已证明。',
                   'source': source[:30000], 'limit': limit,
                   'model': os.environ.get('MATHLIB2_MODEL', '')}
        req = urllib.request.Request(url, json.dumps(payload).encode(),
            {'Content-Type': 'application/json', **({'Authorization': 'Bearer ' + key} if key else {})})
        with urllib.request.urlopen(req, timeout=45) as response:
            data = json.loads(response.read(200000))
        items = data['candidates'][:limit]
        for item in items:
            if not all(isinstance(item.get(k), str) for k in ('statement', 'strategy', 'neg_strategy', 'label')):
                raise ValueError('服务返回的候选格式错误')
        return items


def provider():
    mode = os.environ.get('MATHLIB2_PROVIDER', 'mock')
    if mode not in {'mock', 'http'}:
        raise ValueError('MATHLIB2_PROVIDER 必须为 mock 或 http')
    return MockProvider() if mode == 'mock' else HTTPProvider()
