"""标准库HTTP；不跟随重定向，不读取代理环境变量，子进程限制整个请求时间。"""
import multiprocessing
import time
import urllib.error
import urllib.request

MAX_RESPONSE=262144


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl): return None


def _fetch(pipe, url, payload, headers, timeout):
    start=time.monotonic()
    try:
        opener=urllib.request.build_opener(urllib.request.ProxyHandler({}),NoRedirect())
        request=urllib.request.Request(url,payload,headers,method='POST')
        try:
            response=opener.open(request,timeout=timeout)
        except urllib.error.HTTPError as exc:
            response=exc
        with response:
            raw=response.read(MAX_RESPONSE+1)
            result=dict(http_status=response.code,headers={k.lower():v for k,v in response.headers.items() if k.lower() in ('x-request-id','request-id','retry-after','content-type')},
                        body=raw[:MAX_RESPONSE].decode('utf-8',errors='replace'),truncated=len(raw)>MAX_RESPONSE,error=None)
    except Exception as exc:
        # 异常消息可能含凭证/URL，记录错误类即可。
        result=dict(http_status=None,headers={},body='',truncated=False,error=type(exc).__name__)
    result['transport_elapsed']=time.monotonic()-start
    try: pipe.send(result)
    finally: pipe.close()


class HTTPTransport:
    evidence_kind='live'

    def send(self,url,payload,headers,timeout):
        ctx=multiprocessing.get_context('spawn')
        receive,send=ctx.Pipe(duplex=False)
        worker=ctx.Process(target=_fetch,args=(send,url,payload,headers,timeout),daemon=True)
        start=time.monotonic()
        try:
            worker.start();send.close()
            if receive.poll(timeout):
                try: return receive.recv()
                except EOFError:
                    return dict(http_status=None,headers={},body='',truncated=False,error='worker_exited')
            return dict(http_status=None,headers={},body='',truncated=False,error='deadline_exceeded',transport_elapsed=time.monotonic()-start)
        finally:
            send.close();receive.close()
            if worker.pid:
                if worker.is_alive(): worker.terminate()
                worker.join(timeout=1)
