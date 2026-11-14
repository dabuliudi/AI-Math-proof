import hashlib
import json
import re
import uuid
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import quote


def now(): return datetime.now(timezone.utc).isoformat()


class Audit:
    def __init__(self, root, secret='', kind='live'):
        self.folder=Path(root)/uuid.uuid4().hex
        self.folder.mkdir(parents=True,exist_ok=False)
        self.secret=secret
        self.kind=kind
        self.sequence=0
        self.previous=''

    def clean(self, value):
        if isinstance(value,dict):
            return {k:('[REDACTED]' if k.lower() in ('authorization','api_key','access_token','x-api-key') else self.clean(v)) for k,v in value.items()}
        if isinstance(value,list): return [self.clean(v) for v in value]
        if isinstance(value,str):
            if self.secret:
                # 捕获JSON把ASCII密钥写成\u00XX的常见回显；仅在含密钥时替换原内容。
                decoded=re.sub(r'\\u00([0-9a-fA-F]{2})',lambda m:chr(int(m[1],16)),value)
                if self.secret in decoded: value=decoded
                for token in {self.secret,json.dumps(self.secret)[1:-1],quote(self.secret,safe='')}:
                    value=value.replace(token,'[REDACTED]')
            return re.sub(r'(?i)Bearer\s+[^\s"\\]+','Bearer [REDACTED]',value)
        return value

    def save(self, name, value):
        # 新文件独占创建；失败尝试不覆盖。文件名仅来自网关自身。
        with (self.folder/name).open('x',encoding='utf-8') as f:
            json.dump(self.clean(value),f,ensure_ascii=False,indent=2,allow_nan=False)

    def event(self, kind, **payload):
        self.sequence+=1
        event=self.clean(dict(sequence=self.sequence,time=now(),kind=kind,evidence_kind=self.kind,payload=payload,previous_hash=self.previous))
        digest=hashlib.sha256(json.dumps(event,ensure_ascii=False,sort_keys=True,allow_nan=False).encode()).hexdigest()
        event['hash']=digest;self.previous=digest
        with (self.folder/'events.jsonl').open('a',encoding='utf-8') as f:
            f.write(json.dumps(event,ensure_ascii=False,allow_nan=False)+'\n')
