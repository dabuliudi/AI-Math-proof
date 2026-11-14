import json
import uuid
from dataclasses import replace
from pathlib import Path
from mathlib2_gateway.config import Config
from mathlib2_gateway.__main__ import SMOKE_GOAL

GOAL=SMOKE_GOAL
SECRET='fixture-secret-not-a-real-key'
EVIDENCE=Path(__file__).resolve().parents[1]/'evidence/synthetic'

def folder():
    root=EVIDENCE/uuid.uuid4().hex
    root.mkdir(parents=True,exist_ok=False)
    return root

def config(**kw):
    return replace(Config('responses','https://example.invalid/v1','fixture-model',SECRET,1,2,
                          'synthetic fixture, not actual prices','2026-11-14'),**kw)

def plan(goal=GOAL):
    return dict(goal=goal,strategy='使用序关系传递性；尚未验证。',steps=[dict(id='s1',objective='从两条假设推出目标',reason='待核对传递性定理')],uncertainties=['未执行Lean'])

def response(provider='responses', **kw):
    text=json.dumps(plan(),ensure_ascii=False)
    if provider=='responses':
        result=dict(id='fixture-response',model='fixture-model-snapshot',status='completed',
            output=[dict(type='message',content=[dict(type='output_text',text=text)])],
            usage=dict(input_tokens=200,output_tokens=100))
    else:
        result=dict(id='fixture-response',model='fixture-model-snapshot',
            choices=[dict(finish_reason='stop',message=dict(content=text))],
            usage=dict(prompt_tokens=200,completion_tokens=100))
    result.update(kw)
    return result

def wire(body=None,status=200,headers=None,error=None):
    return dict(http_status=status,headers=headers or {},body=json.dumps(response() if body is None else body,ensure_ascii=False),truncated=False,error=error)

class SyntheticTransport:
    evidence_kind='synthetic_fixture'
    def __init__(self,*results): self.results=list(results);self.calls=[]
    def send(self,*args):
        self.calls.append(args)
        return self.results.pop(0)
