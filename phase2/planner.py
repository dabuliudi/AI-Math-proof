"""通用有界Horn推理与项统一，不读取benchmark标识或答案。"""
from itertools import product
from .model import Atom


def unify(pattern,fact,binding):
    if pattern['op']!=fact.op: return None
    result=dict(binding)
    for key,value in (('left',fact.left),('right',fact.right)):
        term=pattern[key]
        if 'lit' in term:
            if str(term['lit'])!=value: return None
        else:
            variable=term['var']
            if variable in result and result[variable]!=value: return None
            result[variable]=value
    return result


def instantiate(pattern,binding):
    def term(t): return binding[t['var']] if 'var' in t else str(t['lit'])
    return Atom(pattern['op'],term(pattern['left']),term(pattern['right']))


class Planner:
    def __init__(self,rules,problem,match_budget=12000):
        self.rules=rules
        self.problem=problem
        self.match_budget=match_budget
        self.rejected=set()
        self.last_scan=0

    def candidates(self,facts,unresolved):
        candidates=[]; scanned=0
        for rule in self.rules:
            partial=[({},[])]
            for premise in rule['premises']:
                next_partial=[]
                for binding,parents in partial:
                    for atom,node in facts.items():
                        scanned+=1
                        bound=unify(premise,atom,binding)
                        if bound is not None: next_partial.append((bound,parents+[node]))
                        if scanned>=self.match_budget: break
                    if scanned>=self.match_budget: break
                partial=next_partial
                if not partial or scanned>=self.match_budget: break
            for binding,parents in partial:
                if len(parents)!=len(rule['premises']): continue
                missing=[i for i in range(rule['variables']) if i not in binding]
                for values in product(self.problem.terms,repeat=len(missing)):
                    scanned+=1
                    bound={**binding,**dict(zip(missing,values))}
                    conclusion=instantiate(rule['conclusion'],bound)
                    key=(rule['name'],tuple(sorted(bound.items())),tuple(parents))
                    if conclusion not in facts and key not in self.rejected:
                        score=max((100*(conclusion==g)+20*(conclusion.left==g.left)+15*(conclusion.right==g.right)+5*(conclusion.op==g.op)) for g in unresolved)
                        candidates.append(dict(rule=rule,binding=bound,parents=parents,conclusion=conclusion,key=key,score=score))
                    if scanned>=self.match_budget: break
                if scanned>=self.match_budget: break
            if scanned>=self.match_budget: break
        self.last_scan=scanned
        # General source preference, independent of any benchmark or theorem identifier.
        return sorted(candidates,key=lambda c:(-c['score'],len(c['parents']),not c['rule']['module'].startswith('Mathlib.'),c['rule']['name'],c['conclusion'].text()))

    def feedback(self,candidate,result):
        self.rejected.add(candidate['key'])
        output=result['stdout']+result['stderr']
        return 'unknown_declaration' if 'Unknown constant' in output or 'Unknown identifier' in output else ('timeout' if result['status']=='timeout' else 'candidate_rejected')
