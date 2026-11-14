import math
import os
from dataclasses import dataclass, field
from datetime import date
from urllib.parse import urlsplit


class ConfigurationError(ValueError):
    pass


@dataclass(frozen=True)
class Config:
    provider: str
    base_url: str
    model: str
    api_key: str = field(repr=False)
    input_price: float
    output_price: float
    price_source: str
    price_as_of: str
    output_mode: str = 'json_schema'
    chat_token_field: str = 'max_completion_tokens'
    max_attempts: int = 3
    request_timeout: float = 30
    total_timeout: float = 90
    max_input_tokens: int = 8192
    max_output_tokens: int = 1200
    max_total_tokens: int = 30000
    max_cost_usd: float = 0.10
    allow_local_http: bool = False

    def validate(self):
        if self.provider not in ('responses', 'chat_completions'):
            raise ConfigurationError('不支持的协议；请注册新Provider适配器')
        try:
            url = urlsplit(self.base_url)
        except ValueError:
            raise ConfigurationError('地址格式无效') from None
        local = url.hostname in ('127.0.0.1', 'localhost', '::1')
        if (url.scheme != 'https' and not (url.scheme == 'http' and local and self.allow_local_http)) or not url.hostname:
            raise ConfigurationError('地址须为HTTPS；本地HTTP需要显式开启')
        if url.username or url.password or url.query or url.fragment or any(ord(c) < 33 for c in self.base_url):
            raise ConfigurationError('地址不得包含凭证、查询参数、片段或控制字符')
        try:
            url.port
        except ValueError:
            raise ConfigurationError('端口无效') from None
        if not self.api_key or any(ord(c) < 33 or ord(c) > 126 for c in self.api_key):
            raise ConfigurationError('API Key未配置或含非法字符')
        if not self.model or len(self.model) > 200 or any(ord(c) < 32 for c in self.model):
            raise ConfigurationError('模型名未配置或无效')
        if self.output_mode not in ('json_schema', 'json_object', 'prompt_json'):
            raise ConfigurationError('输出模式无效')
        if self.chat_token_field not in ('max_tokens', 'max_completion_tokens'):
            raise ConfigurationError('Chat输出长度参数无效')
        for name, low, high in [('max_attempts',1,5),('max_input_tokens',512,100000),('max_output_tokens',64,16000),('max_total_tokens',576,500000)]:
            value = getattr(self,name)
            if type(value) is not int or not low <= value <= high:
                raise ConfigurationError(name+'超出范围')
        for name, low, high in [('request_timeout',0.1,120),('total_timeout',0.1,600),('input_price',0,10000),('output_price',0,10000),('max_cost_usd',0,10)]:
            value = getattr(self,name)
            if isinstance(value,bool) or not isinstance(value,(int,float)) or not math.isfinite(value) or not low <= value <= high:
                raise ConfigurationError(name+'超出范围或不是有限数')
        if not self.price_source or len(self.price_source)>500:
            raise ConfigurationError('须提供价格来源；缺失费用不能视为0')
        try:
            date.fromisoformat(self.price_as_of)
        except (ValueError,TypeError):
            raise ConfigurationError('价格日期须为YYYY-MM-DD') from None
        return self

    @classmethod
    def from_env(cls, env=None):
        env = os.environ if env is None else env
        def value(name, default=''): return env.get('MATHLIB2_GW_'+name,default)
        required = ['MODEL','API_KEY','INPUT_USD_PER_MILLION','OUTPUT_USD_PER_MILLION','PRICE_SOURCE','PRICE_AS_OF']
        missing = [n for n in required if not value(n)]
        if missing: raise ConfigurationError('缺少环境变量：'+', '.join('MATHLIB2_GW_'+n for n in missing))
        provider = value('PROVIDER','responses')
        base = value('BASE_URL','https://api.openai.com/v1' if provider=='responses' else '')
        try:
            config = cls(provider,base.rstrip('/'),value('MODEL'),value('API_KEY'),
                float(value('INPUT_USD_PER_MILLION')),float(value('OUTPUT_USD_PER_MILLION')),
                value('PRICE_SOURCE'),value('PRICE_AS_OF'),value('OUTPUT_MODE','json_schema'),
                value('CHAT_TOKEN_FIELD','max_completion_tokens'),int(value('MAX_ATTEMPTS','3')),
                float(value('REQUEST_TIMEOUT','30')),float(value('TOTAL_TIMEOUT','90')),
                int(value('MAX_INPUT_TOKENS','8192')),int(value('MAX_OUTPUT_TOKENS','1200')),
                int(value('MAX_TOTAL_TOKENS','30000')),float(value('MAX_COST_USD','0.10')),
                value('ALLOW_LOCAL_HTTP')=='1')
        except ValueError:
            raise ConfigurationError('数字配置无效；未记录配置值以防泄露凭证') from None
        return config.validate()

    def public(self):
        return {k:v for k,v in vars(self).items() if k!='api_key'}
