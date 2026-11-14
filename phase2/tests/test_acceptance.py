"""读取运行证据并独立重编译，不把引擎的accepted字段当作唯一证据。"""
import hashlib
import json
import os
import re
import unittest
import uuid
from pathlib import Path
from phase2.compiler import Compiler,ROOT
from phase2.evidence import Journal,digest
from phase2.model import Problem


@unittest.skipUnless(os.environ.get('MATHLIB2_PHASE2_INTEGRATION')=='1','需要已完成基准及真实Lean')
class AcceptanceTests(unittest.TestCase):
    def test_benchmark_provenance_and_independent_compilation(self):
        batches=sorted((ROOT/'phase2/benchmarks').glob('run-*/summary.json'),key=lambda p:p.stat().st_mtime)
        self.assertTrue(batches,'先运行基准')
        batch=batches[-1].parent
        rows=json.loads((batch/'results.json').read_text(encoding='utf-8'))
        frozen=json.loads((batch/'inputs.json').read_text(encoding='utf-8'))['engine_hashes']
        retrieval_key=digest((ROOT/'phase2/Extract.lean').read_text(encoding='utf-8')+(ROOT/'lean/lake-manifest.json').read_text())
        for name,h in frozen.items():
            self.assertEqual(hashlib.sha256((ROOT/'phase2'/name).read_bytes()).hexdigest(),h)
        journal=Journal(ROOT/'phase2/verification'/uuid.uuid4().hex)
        compiler=Compiler(journal,timeout=90)
        journal.save('environment.json',compiler.metadata())
        checked=[]
        for row in rows:
            result=row['result']; folder=Path(result['run'])
            self.assertEqual(result['ai_calls'],0)
            self.assertFalse(result['candidate_verified'])
            self.assertEqual(result['approval_status'],'pending')
            events=[json.loads(line) for line in (folder/'events.jsonl').read_text(encoding='utf-8').splitlines()]
            previous=''; planned={}; verified=set(); started={}
            for event in events:
                claimed=event.pop('hash')
                self.assertEqual(event['previous_hash'],previous)
                self.assertEqual(claimed,digest(json.dumps(event,ensure_ascii=False,sort_keys=True)))
                previous=claimed; payload=event['payload']
                if event['kind']=='retrieval':self.assertEqual(payload['key'],retrieval_key)
                if event['kind']=='dag_node_planned':
                    node=payload['node']; planned[node['id']]=event['sequence']
                    for parent in payload['parents']:self.assertIn(parent,verified)
                    if node['status']=='assumed':verified.add(node['id'])
                elif event['kind']=='compile_started':
                    name=payload['declarations'][-1]; self.assertLess(planned[name],event['sequence']); started[name]=event['sequence']
                elif event['kind']=='dag_node_updated' and payload['status']=='verified':
                    self.assertIn(payload['node'],started); verified.add(payload['node'])
            for path in folder.glob('attempt-*.json'):
                log=json.loads(path.read_text(encoding='utf-8'))
                self.assertEqual(log['source_sha256'],digest(log['source']))
                self.assertEqual(Path(log['artifact']).read_text(encoding='utf-8'),log['source'])
            if not result['formal_goal_verified']:
                self.assertNotEqual(result['status'],'refuted'); continue
            problem=Problem.parse(json.loads((folder/'problem.json').read_text(encoding='utf-8')))
            final=json.loads(sorted(folder.glob('attempt-*.json'))[-1].read_text(encoding='utf-8'))
            goal=' ∧ '.join(problem.lean(g) for g in problem.goals)
            self.assertIn(f'theorem p2_target {problem.context()} : {goal} := by',final['source'])
            self.assertNotRegex(final['source'],r'\b(?:sorry|admit|axiom)\b')
            names=re.findall(r'^theorem (p2_\w+) ',final['source'],re.M)
            fresh=compiler.check(final['source'],names,goal)
            self.assertTrue(fresh['accepted'],fresh)
            checked.append(dict(case=row['id'],original_run=str(folder),fresh_compile=fresh['log']))
        journal.save('acceptance.json',dict(batch=str(batch),verified=checked,all_passed=True,
            limitation='内部基准的独立证据复核；不是第三方未见问题或LLM能力验收'))
