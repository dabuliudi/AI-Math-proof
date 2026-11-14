import hashlib
import json
import os
import time
import uuid
from decimal import Decimal
from email.utils import parsedate_to_datetime
from pathlib import Path
from .audit import Audit, now
from .config import Config, ConfigurationError
from .contracts import strict_json, validate_plan
from .providers import PROVIDERS, ProtocolError
from .transport import HTTPTransport

DEFAULT_RUNS=Path(__file__).resolve().parent/'runs'
TRANSIENT={408,429,500,502,503,504}
NO_RETRY_CODES={'insufficient_quota','credit_balance_exhausted','organization_spend_limit_exceeded','billing_hard_limit_reached'}


class Ledger:
    """按每次配置输入上限+输出上限保守预占，不把未知用量退款。不是供应商账单保证。"""
    def __init__(self,config):
        self.config=config; self.attempts=0; self.reserved_tokens=0; self.reserved_cost=Decimal(0)
        self.known_tokens=0; self.estimated=Decimal(0); self.unknown_usage=0

    def price(self,a,b):
        return (Decimal(a)*Decimal(str(self.config.input_price))+Decimal(b)*Decimal(str(self.config.output_price)))/Decimal(1000000)

    def reserve(self):
        c=self.config; tokens=c.max_input_tokens+c.max_output_tokens
        price=self.price(c.max_input_tokens,c.max_output_tokens)
        if self.attempts>=c.max_attempts: return 'attempt_budget'
        if self.reserved_tokens+tokens>c.max_total_tokens: return 'token_budget'
        if self.reserved_cost+price>Decimal(str(c.max_cost_usd)): return 'cost_budget'
        self.attempts+=1;self.reserved_tokens+=tokens;self.reserved_cost+=price
        return None

    def settle(self,usage):
        if usage is None:
            self.unknown_usage+=1
            return dict(estimated_usd=None,usage_known=False,limit_violation=False)
        self.known_tokens+=usage['total_tokens']
        amount=self.price(usage['input_tokens'],usage['output_tokens']);self.estimated+=amount
        return dict(estimated_usd=str(amount),usage_known=True,
            limit_violation=usage['input_tokens']>self.config.max_input_tokens or usage['output_tokens']>self.config.max_output_tokens)

    def summary(self):
        return dict(dispatch_attempts=self.attempts,reserved_tokens=self.reserved_tokens,reported_tokens=self.known_tokens,
                    attempts_with_unknown_usage=self.unknown_usage,reserved_usd=str(self.reserved_cost),
                    known_estimated_cost_usd=str(self.estimated),estimated_total_usd=None if self.unknown_usage else str(self.estimated),
                    actual_billed_usd=None,cost_basis='configured_uncached_prices_times_reported_tokens; not invoice',
                    guarantee='local admission reservations only; provider tokenization/pricing/hidden charges not guaranteed')


def retry_delay(header, attempt):
    if header:
        try:
            value=float(header)
            if value>=0 and value<float('inf'): return value
        except ValueError:
            try: return max(0,parsedate_to_datetime(header).timestamp()-time.time())
            except (ValueError,TypeError,OverflowError): pass
    return min(2**(attempt-1),8)


def base_result(status,reason,audit):
    return dict(status=status,reason=reason,run=str(audit.folder),evidence_kind=audit.kind,
                plan=None,generation_origin=None,lean_status='not_run',formal_goal_verified=False,
                candidate_verified=False,approval_status='pending',ai_dispatch_attempts=0,
                http_responses=0,model_responses=0,real_model_responses=0)


def generate_plan(goal,config,root=DEFAULT_RUNS,transport=None):
    config.validate()
    transport=transport or HTTPTransport()
    audit=Audit(root,config.api_key,kind=transport.evidence_kind)
    result=base_result('blocked','preflight',audit)
    ledger=Ledger(config);start=time.monotonic()
    audit.save('config.json',config.public())
    audit.save('goal.json',dict(goal=goal,kind='mathematical_planning_only'))
    audit.save('source-hashes.json',{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in Path(__file__).parent.glob('*.py')})
    audit.event('run_started',model=config.model,provider=config.provider)
    try:
        if not isinstance(goal,str) or not 1<=len(goal.strip())<=2000:
            raise ValueError('目标须为1至2000字符')
        if config.api_key in goal: raise ValueError('目标包含配置密钥，已阻止发送')
        provider=PROVIDERS[config.provider]()
        url,body=provider.build(config,goal)
        payload=json.dumps(body,ensure_ascii=False,allow_nan=False).encode()
        # 字节预筛是保守输入限制，不冒充任意供应商的精确tokenizer。
        if len(payload)>config.max_input_tokens: raise ValueError('请求字节数超过配置输入预占上限')
        audit.save('request-template.json',dict(url=url,body=body,request_bytes=len(payload)))
        result.update(status='failed',reason='no_response')
        while True:
            remaining=config.total_timeout-(time.monotonic()-start)
            if remaining<=0:
                result['reason']='total_deadline';break
            blocked=ledger.reserve()
            if blocked:
                result['reason']=blocked;break
            attempt=ledger.attempts;client_id=uuid.uuid4().hex
            headers={'Content-Type':'application/json','Authorization':'Bearer '+config.api_key,'X-Client-Request-Id':client_id}
            record=dict(attempt=attempt,client_request_id=client_id,started=now(),model_requested=config.model,
                        endpoint=url,request=body,usage=None,metadata=None,plan=None,status='dispatch_started')
            audit.save(f'attempt-{attempt:03d}-request.json',record)
            audit.event('request_dispatch_started',attempt=attempt,client_request_id=client_id)
            sent=time.monotonic()
            try:
                wire=transport.send(url,payload,headers,min(config.request_timeout,remaining))
            except Exception as exc:
                wire=dict(http_status=None,headers={},body='',truncated=False,error=type(exc).__name__)
            record.update(response=wire,elapsed=time.monotonic()-sent,finished=now())
            response=None;plan=None;usage=None;metadata=None;retryable=False
            if wire.get('http_status') is not None: result['http_responses']+=1
            try:
                if wire.get('body'):
                    try: response=strict_json(wire['body'])
                    except ValueError:
                        if wire.get('http_status')!=200:
                            retryable=wire.get('http_status') in TRANSIENT
                            raise ProtocolError('http_'+str(wire['http_status'])) from None
                        raise
                    if not isinstance(response,dict): raise ProtocolError('non_object_response')
                    usage=provider.usage(response);metadata=provider.metadata(response)
                if wire.get('error'):
                    retryable=True;raise ProtocolError('transport_failure')
                status=wire.get('http_status')
                if status!=200:
                    error=response.get('error') if isinstance(response,dict) else None
                    code=error.get('code') if isinstance(error,dict) else None
                    retryable=status in TRANSIENT and code not in NO_RETRY_CODES
                    raise ProtocolError('http_'+str(status))
                if wire.get('truncated'): raise ProtocolError('response_too_large')
                if response is None: raise ProtocolError('empty_response')
                text=provider.text(response)
                if not metadata or not all(isinstance(metadata.get(k),str) and 0<len(metadata[k])<=250 for k in ('response_id','model_reported')):
                    raise ProtocolError('missing_response_identity')
                result['model_responses']+=1
                if audit.kind=='live': result['real_model_responses']+=1
                plan=validate_plan(text,goal)
                record.update(status='plan_generated',plan=plan)
            except (ValueError,TypeError,KeyError,AttributeError,RecursionError) as exc:
                # 固定错误类别；不写jsonschema可能含服务返回秘密的异常描述。
                reason=str(exc) if isinstance(exc,ProtocolError) else 'invalid_structured_output'
                record.update(status='failed',reason=reason)
                result['reason']=reason
            settlement=ledger.settle(usage)
            record.update(usage=usage,metadata=metadata,cost=settlement,actual_billed_usd=None)
            if settlement['limit_violation']:
                record.update(status='failed',reason='reported_usage_exceeded_reservation')
                result['reason']='reported_usage_exceeded_reservation';retryable=False;plan=None
            if time.monotonic()-start>config.total_timeout:
                record.update(status='failed',reason='total_deadline')
                result['reason']='total_deadline';retryable=False;plan=None
            audit.save(f'attempt-{attempt:03d}-response.json',record)
            audit.event('request_finished',attempt=attempt,status=record['status'],response_log=f'attempt-{attempt:03d}-response.json')
            if plan is not None:
                result.update(status='plan_generated',reason='structured_plan_only',plan=plan,
                              generation_origin='AI Generated' if audit.kind=='live' else 'Synthetic Fixture')
                break
            if not retryable: break
            delay=retry_delay(wire.get('headers',{}).get('retry-after'),attempt)
            if ledger.attempts>=config.max_attempts: break
            if delay>=config.total_timeout-(time.monotonic()-start):
                result['reason']='retry_after_exceeds_deadline';break
            audit.event('retry_scheduled',attempt=attempt,delay_seconds=delay)
            time.sleep(delay)
    except (ValueError,ConfigurationError) as exc:
        result.update(status='blocked',reason=str(exc))
        audit.save('preflight-error.json',dict(reason=str(exc),outbound_request=False))
    finally:
        result.update(ai_dispatch_attempts=ledger.attempts,cost=ledger.summary(),elapsed=time.monotonic()-start)
        result=audit.clean(result)
        audit.save('result.json',result);audit.event('run_finished',status=result['status'],reason=result['reason'])
    return result


def run_from_env(goal,root=DEFAULT_RUNS):
    try: config=Config.from_env()
    except ConfigurationError as exc:
        audit=Audit(root,os.environ.get('MATHLIB2_GW_API_KEY',''))
        result=base_result('blocked',str(exc),audit)
        result.update(cost=dict(estimated_total_usd='0',actual_billed_usd='0',reason='no outbound request'))
        audit.save('preflight-error.json',dict(reason=str(exc),outbound_request=False))
        audit.save('result.json',result)
        return result
    return generate_plan(goal,config,root)
