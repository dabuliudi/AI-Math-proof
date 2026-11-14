import json
import threading
import time
import unittest
from http.server import ThreadingHTTPServer,BaseHTTPRequestHandler
from mathlib2_gateway.gateway import generate_plan
from mathlib2_gateway.transport import HTTPTransport
from helpers import config,folder,response,GOAL


class SyntheticHTTPTransport(HTTPTransport):
    evidence_kind='synthetic_fixture'


class Handler(BaseHTTPRequestHandler):
    def log_message(self,*args): pass
    def do_POST(self):
        self.server.requests+=1
        self.server.bodies.append(json.loads(self.rfile.read(int(self.headers['Content-Length']))))
        status,headers,body,delay=self.server.queue.pop(0)
        time.sleep(delay)
        try:
            self.send_response(status)
            for k,v in headers.items():self.send_header(k,v)
            self.end_headers();self.wfile.write(body)
        except (BrokenPipeError,ConnectionResetError,ConnectionAbortedError):pass


class LocalHTTPIntegration(unittest.TestCase):
    def setUp(self):
        self.server=ThreadingHTTPServer(('127.0.0.1',0),Handler)
        self.server.daemon_threads=True;self.server.requests=0;self.server.bodies=[]
        self.thread=threading.Thread(target=self.server.serve_forever,daemon=True);self.thread.start()
        self.config=config(base_url=f'http://127.0.0.1:{self.server.server_port}/v1',allow_local_http=True)
    def tearDown(self):
        self.server.shutdown();self.server.server_close();self.thread.join(2)
    def test_actual_http_retry_then_structured_plan(self):
        self.server.queue=[(503,{'Retry-After':'0'},b'temporarily unavailable',0),
                           (200,{'X-Request-Id':'local-fixture'},json.dumps(response()).encode(),0)]
        r=generate_plan(GOAL,self.config,folder(),SyntheticHTTPTransport())
        self.assertEqual(r['status'],'plan_generated');self.assertEqual(self.server.requests,2)
        self.assertEqual(r['real_model_responses'],0)
        self.assertIn('text',self.server.bodies[1])
    def test_chat_compatible_over_real_local_http(self):
        from dataclasses import replace
        self.server.queue=[(200,{},json.dumps(response('chat_completions')).encode(),0)]
        r=generate_plan(GOAL,replace(self.config,provider='chat_completions'),folder(),SyntheticHTTPTransport())
        self.assertEqual(r['status'],'plan_generated');self.assertIn('response_format',self.server.bodies[0])
    def test_redirect_is_not_followed(self):
        self.server.queue=[(302,{'Location':f'http://127.0.0.1:{self.server.server_port}/steal'},b'redirect',0)]
        r=generate_plan(GOAL,self.config,folder(),SyntheticHTTPTransport())
        self.assertEqual(self.server.requests,1);self.assertEqual(r['status'],'failed')
    def test_request_deadline_kills_worker(self):
        from dataclasses import replace
        self.server.queue=[(200,{},json.dumps(response()).encode(),3)]
        start=time.monotonic()
        r=generate_plan(GOAL,replace(self.config,request_timeout=.4,max_attempts=1),folder(),SyntheticHTTPTransport())
        self.assertLess(time.monotonic()-start,2.5);self.assertEqual(r['status'],'failed')
        self.assertEqual(r['ai_dispatch_attempts'],1)
