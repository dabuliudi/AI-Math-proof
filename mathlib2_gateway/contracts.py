import json
import math
from jsonschema import Draft202012Validator

PLAN_SCHEMA = {
    'type':'object','additionalProperties':False,
    'properties':{
        'goal':{'type':'string','minLength':1,'maxLength':2000},
        'strategy':{'type':'string','minLength':1,'maxLength':2000},
        'steps':{'type':'array','minItems':1,'maxItems':8,'items':{
            'type':'object','additionalProperties':False,
            'properties':{k:{'type':'string','minLength':1,'maxLength':1500} for k in ('id','objective','reason')},
            'required':['id','objective','reason']}},
        'uncertainties':{'type':'array','maxItems':12,'items':{'type':'string','maxLength':1000}}
    },'required':['goal','strategy','steps','uncertainties']}

SYSTEM = ('你是数学规划助手。只给出待验证的数学证明计划，不声称已经检索Mathlib、执行工具或通过Lean。'
          '完整保留目标的定义域、假设和量词；goal必须逐字复述用户目标。仅输出符合给定JSON Schema的JSON。'
          'steps是建议步骤，不是已经构建或验证的DAG。列出不确定点。不要输出或请求执行代码。')


def strict_json(text):
    def pairs(items):
        result={}
        for key,value in items:
            if key in result: raise ValueError('JSON重复字段')
            result[key]=value
        return result
    def invalid(_): raise ValueError('JSON非有限常量')
    def number(value):
        result=float(value)
        if not math.isfinite(result): raise ValueError('JSON非有限数字')
        return result
    return json.loads(text,object_pairs_hook=pairs,parse_constant=invalid,parse_float=number)


def validate_plan(text, goal):
    plan=strict_json(text)
    errors=list(Draft202012Validator(PLAN_SCHEMA).iter_errors(plan))
    if errors: raise ValueError('模型输出不符合Plan Schema')
    if plan['goal']!=goal: raise ValueError('模型改写了目标')
    ids=[s['id'] for s in plan['steps']]
    if len(set(ids))!=len(ids): raise ValueError('步骤ID重复')
    return plan
