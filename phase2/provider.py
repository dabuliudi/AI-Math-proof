"""可选JSON建议网关；本轮未实际调用，不接受可执行代码。"""
import json
import os
import time
import urllib.request
import urllib.error
from datetime import datetime,timezone


class NoAI:
    def suggest(self,goal,prompt,journal):
        journal.event('provider',status='no AI call',goal=goal)
        return []


class HTTPAdvice:
    """协议：POST model/prompt/goal，返回model/version/suggestions/usage。

    仅用于未来规划建议。当前无AI引擎不会实例化此类；不声称已验收真实服务。
    """
    def suggest(self,goal,prompt,journal):
        url=os.environ.get('MATHLIB2_PHASE2_API_URL','')
        model=os.environ.get('MATHLIB2_PHASE2_MODEL','')
        if not model or not url.startswith(('https://','http://127.0.0.1:','http://localhost:')):
            raise ValueError('未配置模型或受支持网关；不要在聊天中发送密钥')
        request=urllib.request.Request(url,json.dumps(dict(model=model,prompt=prompt,goal=goal)).encode(),headers={
            'Content-Type':'application/json','Authorization':'Bearer '+os.environ.get('MATHLIB2_PHASE2_API_KEY','')})
        record=dict(model_requested=model,model_reported=None,model_version=None,prompt=prompt,goal=goal,
                    started=datetime.now(timezone.utc).isoformat(),usage=None,cost=None,output=None,
                    generated_lean_code=None,compile_result=None,status='started')
        index=journal.event('ai_call_started',**record); start=time.perf_counter()
        try:
            with urllib.request.urlopen(request,timeout=45) as response:
                raw=response.read(200001)
            record['output']=raw.decode('utf-8',errors='replace')
            if len(raw)>200000: raise ValueError('模型响应超过200KB')
            result=json.loads(record['output'])
            suggestions=result.get('suggestions')
            if not isinstance(suggestions,list) or len(suggestions)>20 or not all(isinstance(s,str) and len(s)<3000 for s in suggestions):
                raise ValueError('模型响应不符合受限建议协议')
            record.update(model_reported=result.get('model'),model_version=result.get('version'),usage=result.get('usage'),
                          cost=result.get('cost'),status='advice_only_not_executed')
            return suggestions
        except (ValueError,OSError,urllib.error.URLError) as exc:
            record.update(status='failed',error=type(exc).__name__)
            raise
        finally:
            record['elapsed']=time.perf_counter()-start
            journal.save(f'ai-call-{index}.json',record)
            journal.event('ai_call_finished',call=index,status=record['status'],audit=f'ai-call-{index}.json')
