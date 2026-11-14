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
    def __init__(self,rules,problem,match_budget=12000,closure_budget=3000000):
        self.rules=rules
        self.problem=problem
        self.match_budget=match_budget
        self.rejected=set()
        self.last_scan=0
        self.closure_budget=closure_budget
        self.last_plan=dict(mode='none')


    def closure(self,facts,unresolved):
        """内存中的前向饱和（不调用Lean）：返回 (备选推导表, 是否到达不动点, 扫描量)。

        半朴素求值：第一层之后，每条匹配至少用到一个上一层新得到的原子，避免重复连接。
        备选推导表 atom -> [父原子元组,...]，只用于给候选排序；
        每个被采用的结论仍须逐条通过真实Lean编译才能成为事实。
        """
        known=set(facts); alternatives={}; scanned=0; goals=set(unresolved); complete=False
        by_op={}
        for atom in known: by_op.setdefault(atom.op,[]).append(atom)
        frontier=None  # None 表示第一层：所有事实都算“新”
        extra=0
        while True:
            fresh={}; delta_by_op={}
            if frontier is not None:
                for atom in frontier: delta_by_op.setdefault(atom.op,[]).append(atom)
            for rule in self.rules:
                premises=rule['premises']
                if frontier is None: pivots=[None]
                elif not premises: continue
                else: pivots=range(len(premises))
                for pivot in pivots:
                    partial=[({},())]
                    for index,premise in enumerate(premises):
                        # pivot 位置取新原子；之前的位置只取旧原子，之后的位置取全部，保证每个组合恰好枚举一次。
                        if pivot is None or index>pivot: pool=by_op.get(premise['op'],())
                        elif index==pivot: pool=delta_by_op.get(premise['op'],())
                        else: pool=[a for a in by_op.get(premise['op'],()) if a not in frontier]
                        next_partial=[]
                        for binding,parents in partial:
                            for atom in pool:
                                scanned+=1
                                bound=unify(premise,atom,binding)
                                if bound is not None: next_partial.append((bound,parents+(atom,)))
                        partial=next_partial
                        if not partial or scanned>=self.closure_budget: break
                    if scanned>=self.closure_budget: break
                    for binding,parents in partial:
                        if len(parents)!=len(premises): continue
                        missing=[i for i in range(rule['variables']) if i not in binding]
                        for values in product(self.problem.terms,repeat=len(missing)):
                            scanned+=1
                            bound={**binding,**dict(zip(missing,values))}
                            conclusion=instantiate(rule['conclusion'],bound)
                            if conclusion in facts: continue
                            if all(parent in facts for parent in parents):
                                key=(rule['name'],tuple(sorted(bound.items())),tuple(facts[parent] for parent in parents))
                                if key in self.rejected: continue
                            if conclusion in known:
                                options=alternatives[conclusion]
                                if extra and parents not in options and len(options)<16: options.append(parents)
                                continue
                            options=fresh.setdefault(conclusion,[])
                            if parents not in options and len(options)<16: options.append(parents)
                if scanned>=self.closure_budget: break
            if scanned>=self.closure_budget: break
            if not fresh: complete=True; break
            alternatives.update(fresh)
            frontier=set(fresh)
            for atom in fresh:
                known.add(atom); by_op.setdefault(atom.op,[]).append(atom)
            # 目标首次全部出现后再多推两层：最浅的推导未必引理最少，多看两层才能选到更省编译的路径。
            if goals<=known:
                extra+=1
                if extra>2: break
        return alternatives,complete,scanned

    def relevant(self,facts,unresolved):
        """目标在符号闭包中的祖先集合（取新增引理数最少的推导）；到达不动点仍推不出的目标记为 unreachable。"""
        alternatives,complete,scanned=self.closure(facts,unresolved)
        # 树代价：事实为0，新原子为 1+父代价之和；松弛到稳定后每个原子选代价最小的推导。
        cost={atom:0 for atom in facts}; choice={}
        changed=True
        while changed:
            changed=False
            for atom,options in alternatives.items():
                for parents in options:
                    if all(parent in cost for parent in parents):
                        value=1+sum(cost[parent] for parent in parents)
                        if value<cost.get(atom,float('inf')):
                            cost[atom]=value; choice[atom]=parents; changed=True
        useful=set(); stack=[g for g in unresolved if g in choice]
        while stack:
            atom=stack.pop()
            if atom in useful or atom in facts: continue
            useful.add(atom); stack.extend(choice[atom])
        unreachable=[g for g in unresolved if g not in choice]
        self.last_plan=dict(mode='symbolic_closure',closure_scans=scanned,fixpoint=complete,derived=len(alternatives),
            planned_lemmas=len(useful),unreachable=[g.text() for g in unreachable])
        return useful,unreachable,complete

    def candidates(self,facts,unresolved):
        useful,unreachable,complete=self.relevant(facts,unresolved)
        if complete and not useful:
            # 片段内已穷尽且没有任何目标可推出：不再花编译预算去验证无关事实。
            self.last_scan=0; return []
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
                        if conclusion in useful: score+=1000
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
