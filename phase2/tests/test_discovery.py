import json
import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from phase2.model import Problem,Atom
from phase2.planner import Planner,unify,instantiate
from phase2.evidence import Journal,DynamicDAG,digest
from phase2.compiler import Compiler,ROOT,IMPORT
from phase2.engine import discover
from phase2.provider import NoAI,HTTPAdvice


class UnitTests(unittest.TestCase):
    def test_parser_and_injection_boundary(self):
        p=Problem.parse(dict(domain='Nat',variables=['a','b'],assumptions=['a <= b'],goals=['a ≤ b']))
        self.assertEqual(p.goals,p.assumptions)
        self.assertEqual(p.lean(p.goals[0]),'(p2v0 ≤ p2v1)')
        for bad in ('a ≤ b\naxiom bad : False','a + 1 ≤ b','a ≤ z'):
            with self.assertRaises(ValueError):Problem.parse(dict(domain='Nat',variables=['a','b'],goals=[bad]))
        with self.assertRaises(ValueError):Problem.parse(dict(domain='Polynomial',variables=['a'],goals=['a = a']))
        with self.assertRaises(ValueError):Problem.parse(dict(domain='Nat',variables=['a'],goals=['a = a'],proof='prewritten'))

    def test_generic_unification(self):
        pattern=dict(op='∣',left={'var':0},right={'var':1})
        bound=unify(pattern,Atom('∣','a','b'),{})
        self.assertEqual(instantiate(pattern,bound),Atom('∣','a','b'))
        self.assertIsNone(unify(pattern,Atom('≤','a','b'),{}))
        self.assertIsNone(unify(pattern,Atom('∣','c','d'),{0:'a'}))

    def test_dag_planning_journal_precedes_result(self):
        with tempfile.TemporaryDirectory() as tmp:
            journal=Journal(Path(tmp)/'run'); dag=DynamicDAG(journal)
            dag.add('h0','a ≤ b',status='assumed'); dag.add('n1','a ≤ c',['h0'])
            dag.update('n1','verified')
            with self.assertRaises(ValueError):dag.add('h0','cycle',['n1'])
            self.assertEqual(dag.snapshot()['depth'],1)
            events=[json.loads(s) for s in (journal.folder/'events.jsonl').read_text(encoding='utf-8').splitlines()]
            previous=''
            for e in events:
                self.assertEqual(e['previous_hash'],previous)
                actual=e.pop('hash'); self.assertEqual(actual,digest(json.dumps(e,ensure_ascii=False,sort_keys=True))); previous=actual

    def test_provider_no_call_and_unconfigured_http(self):
        with tempfile.TemporaryDirectory() as tmp:
            journal=Journal(Path(tmp)/'run')
            self.assertEqual(NoAI().suggest('goal','prompt',journal),[])
            with patch.dict(os.environ,{},clear=True):
                with self.assertRaises(ValueError):HTTPAdvice().suggest('goal','prompt',journal)

    def test_engine_has_no_legacy_templates_or_benchmark_imports(self):
        for name in ('engine.py','planner.py','compiler.py','retrieval.py'):
            source=(ROOT/'phase2'/name).read_text(encoding='utf-8')
            for banned in ('mason_lemma','Lemma3.lean','from mathlib2.','suite.json','direct_reuse','multilayer'):
                self.assertNotIn(banned,source)


@unittest.skipUnless(os.environ.get('MATHLIB2_PHASE2_INTEGRATION')=='1','需要真实Lean')
class RealLeanTests(unittest.TestCase):
    def test_runtime_intermediates_and_goal_order(self):
        # A renamed problem; no proof or theorem name supplied to the engine.
        result=discover(dict(domain='Nat',variables=['u','v','w','z'],assumptions=['w ∣ z','u ∣ v','v ∣ w'],goals=['u ∣ z']),budget=8)
        self.assertTrue(result['formal_goal_verified'],result)
        self.assertGreaterEqual(result['metrics']['intermediate_lemmas'],1)
        self.assertFalse(result['candidate_verified'])
        self.assertEqual(result['approval_status'],'pending')
        folder=Path(result['run']); events=[json.loads(s) for s in (folder/'events.jsonl').read_text(encoding='utf-8').splitlines()]
        planned={e['payload']['node']['id']:e['sequence'] for e in events if e['kind']=='dag_node_planned'}
        for e in events:
            if e['kind']=='compile_started':
                self.assertLess(planned[e['payload']['declarations'][-1]],e['sequence'])

    def test_real_failure_feedback_and_alternative(self):
        # Fault injection into a retrieved catalog; never a mocked compiler result or benchmark success.
        catalog=json.loads((ROOT/'phase2/library.json').read_text(encoding='utf-8'))['rules']
        reflexive=[r for r in catalog if r['variables']==1 and not r['premises'] and r['conclusion']==dict(op='≤',left={'var':0},right={'var':0})]
        self.assertTrue(reflexive)
        broken={**reflexive[0],'name':'A_missing_declaration'}
        with patch('phase2.engine.load_rules',return_value=[broken,reflexive[0]]):
            result=discover(dict(domain='Nat',variables=['q'],assumptions=[],goals=['q ≤ q']),budget=4)
        self.assertTrue(result['formal_goal_verified'],result)
        self.assertEqual(result['metrics']['failed_compilations'],1)
        self.assertEqual(result['metrics']['repair_attempts'],1)
        failure=json.loads((Path(result['run'])/'attempt-001.json').read_text(encoding='utf-8'))
        self.assertNotEqual(failure['returncode'],0)
        self.assertFalse(failure['accepted'])

    def test_false_goal_never_proved(self):
        result=discover(dict(domain='Nat',variables=['q'],assumptions=[],goals=['q < q']),budget=1)
        self.assertEqual(result['status'],'unknown')
        self.assertFalse(result['formal_goal_verified'])
        self.assertEqual(result['ai_calls'],0)


if __name__=='__main__':unittest.main()
