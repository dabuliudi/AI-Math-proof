"""协议适配器：只构造请求/归一化响应，无网络、无数据库、无代码执行。"""
import json
from abc import ABC, abstractmethod
from .contracts import PLAN_SCHEMA, SYSTEM


class ProtocolError(ValueError):
    pass


def usage_record(raw, input_key, output_key):
    if not isinstance(raw,dict): return None
    a,b=raw.get(input_key),raw.get(output_key)
    if type(a) is not int or type(b) is not int or a<0 or b<0: return None
    details=raw.get('input_tokens_details',raw.get('prompt_tokens_details')) or {}
    cached=details.get('cached_tokens') if isinstance(details,dict) else None
    if cached is not None and (type(cached) is not int or not 0<=cached<=a): return None
    # 完整原始usage保留在HTTP body；这里只保留受检标量，避免任意嵌套元数据进入日志结构。
    return dict(input_tokens=a,output_tokens=b,total_tokens=a+b,cached_input_tokens=cached)


class Provider(ABC):
    @abstractmethod
    def build(self, config, goal): pass

    @abstractmethod
    def usage(self, body): pass

    @abstractmethod
    def text(self, body): pass

    def metadata(self, body):
        def text(key):
            value=body.get(key)
            return value if isinstance(value,str) and len(value)<=250 else None
        return dict(response_id=text('id'),model_reported=text('model'),
                    model_version=text('model_version'),system_fingerprint=text('system_fingerprint'))

    def messages(self, config, goal):
        prompt=SYSTEM
        if config.output_mode!='json_schema': prompt+='\nJSON Schema:\n'+json.dumps(PLAN_SCHEMA,ensure_ascii=False)
        return [{'role':'system','content':prompt},{'role':'user','content':goal}]


class ResponsesProvider(Provider):
    def build(self, config, goal):
        body=dict(model=config.model,input=self.messages(config,goal),max_output_tokens=config.max_output_tokens,store=False,stream=False)
        if config.output_mode=='json_schema':
            body['text']={'format':dict(type='json_schema',name='math_plan',strict=True,schema=PLAN_SCHEMA)}
        elif config.output_mode=='json_object': body['text']={'format':{'type':'json_object'}}
        return config.base_url+'/responses',body

    def usage(self, body): return usage_record(body.get('usage'),'input_tokens','output_tokens')

    def text(self, body):
        if body.get('status')!='completed': raise ProtocolError('response_not_completed')
        output=body.get('output')
        if not isinstance(output,list): raise ProtocolError('missing_output')
        chunks=[]
        for item in output:
            if not isinstance(item,dict): raise ProtocolError('invalid_output')
            if item.get('type')=='reasoning': continue
            if item.get('type')!='message': raise ProtocolError('unexpected_tool_or_output')
            for part in item.get('content',[]):
                if part.get('type')=='refusal': raise ProtocolError('model_refusal')
                if part.get('type')!='output_text' or not isinstance(part.get('text'),str): raise ProtocolError('invalid_content')
                chunks.append(part['text'])
        if not chunks: raise ProtocolError('empty_output')
        return ''.join(chunks)


class ChatCompletionsProvider(Provider):
    def build(self, config, goal):
        body=dict(model=config.model,messages=self.messages(config,goal),stream=False)
        body[config.chat_token_field]=config.max_output_tokens
        if config.output_mode=='json_schema':
            body['response_format']=dict(type='json_schema',json_schema=dict(name='math_plan',strict=True,schema=PLAN_SCHEMA))
        elif config.output_mode=='json_object': body['response_format']={'type':'json_object'}
        return config.base_url+'/chat/completions',body

    def usage(self, body): return usage_record(body.get('usage'),'prompt_tokens','completion_tokens')

    def text(self, body):
        choices=body.get('choices')
        if not isinstance(choices,list) or len(choices)!=1: raise ProtocolError('invalid_choices')
        c=choices[0]
        if c.get('finish_reason')!='stop': raise ProtocolError('response_not_completed')
        msg=c.get('message',{})
        if msg.get('refusal'): raise ProtocolError('model_refusal')
        if msg.get('tool_calls') or msg.get('function_call'): raise ProtocolError('unexpected_tool_call')
        if not isinstance(msg.get('content'),str): raise ProtocolError('missing_content')
        return msg['content']


PROVIDERS={'responses':ResponsesProvider,'chat_completions':ChatCompletionsProvider}
