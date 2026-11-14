"""受限数学输入；不把结构解析称作自然语言语义理解。"""
from dataclasses import dataclass
import re


@dataclass(frozen=True)
class Atom:
    op: str
    left: str
    right: str

    def text(self):
        return f'{self.left} {self.op} {self.right}'


@dataclass
class Problem:
    variables: list[str]
    assumptions: list[Atom]
    goals: list[Atom]
    original_text: str = ''

    @classmethod
    def parse(cls, data):
        if set(data)-{'domain','variables','assumptions','goals','original_text'}:
            raise ValueError('Blind输入仅允许问题字段，不接受证明、策略或预置DAG')
        if data.get('domain') != 'Nat':
            raise ValueError('目前只支持明确的Nat结构输入；其他语义不猜测')
        variables = data['variables']
        if not 0 < len(variables) <= 8 or len(set(variables)) != len(variables):
            raise ValueError('变量必须唯一，数量1–8')
        if any(not isinstance(x,str) or not re.fullmatch(r'[a-z][a-z0-9_]{0,30}',x) for x in variables):
            raise ValueError('变量名无效')
        def atom(text):
            if not isinstance(text,str) or len(text)>160:
                raise ValueError('关系长度无效')
            match = re.fullmatch(r'\s*([a-z][a-z0-9_]*|[0-9]+)\s*(≤|<=|<|∣|=)\s*([a-z][a-z0-9_]*|[0-9]+)\s*',text)
            if not match:
                raise ValueError('支持变量/常数之间的≤、<、∣、=；不执行任意Lean输入')
            left,op,right=match.groups()
            for term in (left,right):
                if term not in variables and (not term.isdigit() or int(term)>10000):
                    raise ValueError('未绑定变量或常数超出范围')
            return Atom('≤' if op=='<=' else op,left,right)
        assumptions=[atom(x) for x in data.get('assumptions',[])]
        goals=[atom(x) for x in data['goals']]
        if len(assumptions)>12 or not 1<=len(goals)<=4:
            raise ValueError('假设最多12个，合取目标1–4个')
        return cls(variables,assumptions,goals,str(data.get('original_text',''))[:20000])

    @property
    def terms(self):
        return sorted(set(self.variables+['0','1']+[t for a in self.assumptions+self.goals for t in (a.left,a.right)]))

    def term_lean(self,term):
        return f'p2v{self.variables.index(term)}' if term in self.variables else str(int(term))

    def lean(self,atom):
        return f'({self.term_lean(atom.left)} {atom.op} {self.term_lean(atom.right)})'

    def context(self):
        return ' '.join([f'(p2v{i} : Nat)' for i in range(len(self.variables))]+[f'(h{i} : {self.lean(a)})' for i,a in enumerate(self.assumptions)])

    def arguments(self):
        return ' '.join([f'p2v{i}' for i in range(len(self.variables))]+[f'h{i}' for i in range(len(self.assumptions))])
