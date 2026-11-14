import json
import os
import unittest
from dataclasses import replace
from pathlib import Path
from unittest.mock import patch
from mathlib2_gateway.config import Config, ConfigurationError
from mathlib2_gateway.contracts import strict_json, validate_plan
from mathlib2_gateway.gateway import generate_plan,run_from_env,Ledger,retry_delay
from mathlib2_gateway.providers import PROVIDERS,ProtocolError,usage_record
from mathlib2_gateway.audit import Audit
from helpers import config,folder,plan,response,wire,SyntheticTransport,GOAL,SECRET


class GatewayUnits(unittest.TestCase):
    def test_config_env_and_secret_repr(self):
        env={'MATHLIB2_GW_MODEL':'chosen-model','MATHLIB2_GW_API_KEY':SECRET,
             'MATHLIB2_GW_INPUT_USD_PER_MILLION':'1','MATHLIB2_GW_OUTPUT_USD_PER_MILLION':'2',
             'MATHLIB2_GW_PRICE_SOURCE':'test-only','MATHLIB2_GW_PRICE_AS_OF':'2026-11-14'}
        c=Config.from_env(env)
        self.assertEqual(c.model,'chosen-model');self.assertNotIn(SECRET,repr(c));self.assertNotIn('api_key',c.public())
        for change in ({'api_key':''},{'input_price':float('nan')},{'max_attempts':True},{'price_as_of':'bad'},
                       {'base_url':'https://user:pass@example.test/v1'},{'base_url':'https://example.test/?key=x'},
                       {'base_url':'https://['},{'base_url':'http://example.test/v1'},{'base_url':'http://127.0.0.1/v1'},
                       {'chat_token_field':'unbounded_tokens'}):
            with self.subTest(change=change),self.assertRaises(ConfigurationError): replace(c,**change).validate()
        replace(c,base_url='http://127.0.0.1:8080/v1',allow_local_http=True).validate()

    def test_unconfigured_preflight_has_no_fake_call(self):
        with patch.dict(os.environ,{},clear=True): result=run_from_env(GOAL,folder())
        self.assertEqual(result['status'],'blocked');self.assertEqual(result['ai_dispatch_attempts'],0)
        self.assertEqual(result['real_model_responses'],0)
        self.assertTrue((Path(result['run'])/'preflight-error.json').exists())

    def test_protocols_modes_and_no_tools(self):
        for name,cls in PROVIDERS.items():
            for mode in ('json_schema','json_object','prompt_json'):
                c=config(provider=name,output_mode=mode);url,body=cls().build(c,GOAL)
                self.assertTrue(url.startswith(c.base_url));self.assertNotIn('tools',body)
                self.assertNotIn('api_key',body);self.assertEqual(body['model'],c.model)
                self.assertEqual(validate_plan(cls().text(response(name)),GOAL)['goal'],GOAL)
        self.assertIn('max_tokens',PROVIDERS['chat_completions']().build(config(chat_token_field='max_tokens'),GOAL)[1])

    def test_strict_json_schema_target_and_duplicate_keys(self):
        for text in ('{"a":1,"a":2}','{"x":NaN}','{"x":1e999}',json.dumps({**plan(),'verified':True}),
                     json.dumps(plan(goal='different')),json.dumps({**plan(),'steps':[]})):
            with self.subTest(text=text),self.assertRaises(ValueError):validate_plan(text,GOAL)
        with self.assertRaises(ValueError):strict_json('{"x":Infinity}')

    def test_refusal_incomplete_missing_and_tool_output(self):
        examples=[response(status='incomplete'),response(output=[]),
            response(output=[dict(type='function_call')]),response(output=[dict(type='message',content=[dict(type='refusal',refusal='no')])])]
        for item in examples:
            with self.assertRaises(ProtocolError):PROVIDERS['responses']().text(item)
        with self.assertRaises(ProtocolError):PROVIDERS['chat_completions']().text(response('chat_completions',choices=[dict(finish_reason='length')]))

    def test_usage_validation_and_model_version_not_invented(self):
        for u in ({'input_tokens':True,'output_tokens':3},{'input_tokens':-1,'output_tokens':2},None):
            self.assertIsNone(usage_record(u,'input_tokens','output_tokens'))
        self.assertIsNone(PROVIDERS['responses']().metadata(response())['model_version'])

    def test_success_is_only_fixture_plan_not_lean(self):
        t=SyntheticTransport(wire());r=generate_plan(GOAL,config(),folder(),t)
        self.assertEqual(r['status'],'plan_generated');self.assertEqual(r['generation_origin'],'Synthetic Fixture')
        self.assertEqual(r['real_model_responses'],0);self.assertFalse(r['formal_goal_verified'])
        self.assertFalse(r['candidate_verified']);self.assertEqual(r['lean_status'],'not_run');self.assertEqual(r['approval_status'],'pending')
        self.assertEqual(r['cost']['estimated_total_usd'],'0.0004');self.assertIsNone(r['cost']['actual_billed_usd'])

    def test_auth_failure_not_retried_and_echo_secret_redacted(self):
        t=SyntheticTransport(wire({'error':{'message':'Bearer '+SECRET,'api_key':SECRET}},401))
        r=generate_plan(GOAL,config(),folder(),t)
        self.assertEqual(len(t.calls),1);self.assertEqual(r['status'],'failed')
        for f in Path(r['run']).glob('*'):
            self.assertNotIn(SECRET,f.read_text(encoding='utf-8'))
        self.assertTrue((Path(r['run'])/'attempt-001-response.json').exists())

    def test_transient_retry_and_failed_attempt_preserved(self):
        t=SyntheticTransport(wire({'error':{'code':'rate_limit_error'}},429,{'retry-after':'0'}),wire())
        r=generate_plan(GOAL,config(),folder(),t)
        self.assertEqual(r['status'],'plan_generated');self.assertEqual(len(t.calls),2)
        first=json.loads((Path(r['run'])/'attempt-001-response.json').read_text(encoding='utf-8'))
        self.assertEqual(first['status'],'failed');self.assertIsNone(r['cost']['estimated_total_usd'])
        self.assertEqual(r['cost']['attempts_with_unknown_usage'],1)

    def test_html_503_retry_and_quota_not_retried(self):
        item=wire(status=503,headers={'retry-after':'0'});item['body']='<html>down</html>'
        r=generate_plan(GOAL,config(),folder(),SyntheticTransport(item,wire()))
        self.assertEqual(r['ai_dispatch_attempts'],2)
        t=SyntheticTransport(wire({'error':{'code':'insufficient_quota'}},429))
        r=generate_plan(GOAL,config(),folder(),t);self.assertEqual(len(t.calls),1)

    def test_budget_prevents_dispatch_and_unknown_usage_keeps_reservation(self):
        for c in (config(max_cost_usd=0),config(max_total_tokens=576)):
            t=SyntheticTransport();r=generate_plan(GOAL,c,folder(),t)
            self.assertEqual(len(t.calls),0);self.assertEqual(r['ai_dispatch_attempts'],0)
        ledger=Ledger(config(max_attempts=2,max_total_tokens=9392))
        self.assertIsNone(ledger.reserve());ledger.settle(None)
        self.assertEqual(ledger.reserve(),'token_budget');self.assertEqual(ledger.summary()['attempts_with_unknown_usage'],1)

    def test_missing_usage_preserved_and_overreported_usage_stops(self):
        r=generate_plan(GOAL,config(),folder(),SyntheticTransport(wire(response(usage=None))))
        self.assertEqual(r['status'],'plan_generated');self.assertIsNone(r['cost']['estimated_total_usd'])
        r=generate_plan(GOAL,config(),folder(),SyntheticTransport(wire(response(usage=dict(input_tokens=999999,output_tokens=1)))))
        self.assertEqual(r['reason'],'reported_usage_exceeded_reservation');self.assertIsNone(r['plan'])

    def test_long_retry_after_respects_total_deadline(self):
        t=SyntheticTransport(wire({},503,{'retry-after':'600'}))
        r=generate_plan(GOAL,config(total_timeout=1),folder(),t)
        self.assertEqual(r['reason'],'retry_after_exceeds_deadline');self.assertEqual(len(t.calls),1)
        self.assertEqual(retry_delay('0',1),0);self.assertEqual(retry_delay(None,2),2)

    def test_input_secret_and_oversize_never_sent(self):
        for goal in (SECRET,'a'*2001):
            t=SyntheticTransport();r=generate_plan(goal,config(),folder(),t)
            self.assertEqual(r['status'],'blocked');self.assertEqual(len(t.calls),0)

    def test_malformed_response_identity_and_schema_failures_saved(self):
        cases=[wire(response(id=None)),wire(response(output=[dict(type='message',content=[dict(type='output_text',text='{}')])]))]
        huge=wire();huge['truncated']=True;cases.append(huge)
        for item in cases:
            r=generate_plan(GOAL,config(),folder(),SyntheticTransport(item))
            self.assertEqual(r['status'],'failed');self.assertIsNone(r['plan'])
            self.assertTrue((Path(r['run'])/'attempt-001-response.json').exists())

    def test_no_database_lean_or_old_engine_dependencies(self):
        root=Path(__file__).resolve().parents[1]
        for p in root.glob('*.py'):
            text=p.read_text(encoding='utf-8')
            for bad in ('import sqlite3','from mathlib2.','from phase2.','import subprocess','eval(','exec('):
                self.assertNotIn(bad,text)

    def test_audit_hash_chain_unicode_secret_and_unique_runs(self):
        import hashlib
        root=folder();audit=Audit(root,SECRET,kind='synthetic_fixture')
        escaped=''.join('\\u%04x'%ord(c) for c in SECRET)
        audit.event('failure',raw='{"error":"'+escaped+'"}')
        audit.event('done',value=1)
        previous=''
        for line in (audit.folder/'events.jsonl').read_text(encoding='utf-8').splitlines():
            event=json.loads(line);actual=event.pop('hash')
            self.assertEqual(event['previous_hash'],previous)
            self.assertEqual(actual,hashlib.sha256(json.dumps(event,ensure_ascii=False,sort_keys=True).encode()).hexdigest())
            previous=actual
            self.assertNotIn(SECRET,str(event));self.assertNotIn(escaped,str(event))
        other=Audit(root,SECRET);self.assertNotEqual(audit.folder,other.folder)
        audit.save('once.json',{} )
        with self.assertRaises(FileExistsError):audit.save('once.json',{})

    def test_transport_exception_retains_attempt(self):
        class FailingTransport:
            evidence_kind='synthetic_fixture'
            def send(self,*args):raise OSError(SECRET)
        r=generate_plan(GOAL,config(max_attempts=1),folder(),FailingTransport())
        self.assertEqual(r['status'],'failed');self.assertEqual(r['cost']['attempts_with_unknown_usage'],1)
        path=Path(r['run'])/'attempt-001-response.json'
        self.assertTrue(path.exists());self.assertNotIn(SECRET,path.read_text(encoding='utf-8'))
