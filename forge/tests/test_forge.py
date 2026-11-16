"""forge 的测试。纯逻辑部分总是运行；需要真实 Lean 的部分设置 FORGE_INTEGRATION=1 才运行，且不修改库和队列。"""
import json
import os
import tempfile
import threading
import unittest
import uuid
from pathlib import Path
from unittest import mock

from forge import insight, tasks
from forge.statement import StatementError, analyse_submission, closed_form, split_signature, strip_comments


class StatementTests(unittest.TestCase):
    def test_split_at_first_top_level_colon(self):
        self.assertEqual(split_signature('(a b : ℕ) (h : a ∣ b) : a ≤ b'), ('(a b : ℕ) (h : a ∣ b)', 'a ≤ b'))
        self.assertEqual(split_signature(': ∀ n : ℕ, n = n'), ('', '∀ n : ℕ, n = n'))
        self.assertEqual(closed_form('{α : Type*} [Group α] (x : α) : x = x'), '∀ {α : Type*} [Group α] (x : α), x = x')
        self.assertEqual(closed_form(': 1 + 1 = 2'), '1 + 1 = 2')
        for bad in ('(a : ℕ)', '(a : ℕ) : a = a := rfl', '(a : ℕ) :'):
            with self.assertRaises(StatementError):
                split_signature(bad)

    def test_comments_and_strings_do_not_hide_or_trigger_keywords(self):
        self.assertNotIn('sorry', strip_comments('x -- sorry\n/- sorry /- nested sorry -/ -/ y "sorry"'))
        ok = 'theorem foo (n : ℕ) : n = n := by\n  -- not a sorry\n  rfl\n'
        self.assertEqual(analyse_submission(ok, 'foo'), ['foo'])

    def test_submission_rejects_escape_hatches(self):
        cases = {
            'theorem foo : True := by\n  sorry\n': 'sorry',
            'axiom cheat : False\ntheorem foo : True := trivial\n': 'axiom',
            'instance : LT ℕ := ⟨fun _ _ => True⟩\ntheorem foo : True := trivial\n': 'instance',
            'theorem foo : True := by\n  native_decide\n': 'native_decide',
            'set_option maxHeartbeats 0\ntheorem foo : True := trivial\n': 'set_option',
            'theorem foo : True := by\n  run_tac pure ()\n': 'run_tac',
            'local notation "X" => True\ntheorem foo : X := trivial\n': 'notation',
            'theorem foo : True := by\n  simp [local foo]\n': 'local',
        }
        for body, word in cases.items():
            with self.assertRaises(StatementError) as caught:
                analyse_submission(body, 'foo')
            self.assertIn(word, str(caught.exception))

    def test_submission_naming_rules(self):
        helper = 'lemma foo_aux1 : True := trivial\ntheorem foo : True := foo_aux1\n'
        self.assertEqual(analyse_submission(helper, 'foo'), ['foo_aux1', 'foo'])
        with self.assertRaises(StatementError):  # 主定理必须最后
            analyse_submission('theorem foo : True := trivial\nlemma foo_aux1 : True := trivial\n', 'foo')
        with self.assertRaises(StatementError):  # 辅助引理不能占用别的名字
            analyse_submission('lemma bar : True := trivial\ntheorem foo : True := bar\n', 'foo')
        with self.assertRaises(StatementError):  # 证伪须用 _disproof 名
            analyse_submission('theorem foo : True := trivial\n', 'foo', disproof=True)
        self.assertEqual(analyse_submission('theorem foo_disproof : ¬ False := id\n', 'foo', disproof=True), ['foo_disproof'])
        with self.assertRaises(StatementError):  # 顶格只能是声明或 open
            analyse_submission('theorem foo : True := by\ntrivial\n', 'foo')

    def test_numeral_fraction_exponent_is_flagged(self):
        from forge.statement import lint_statement
        self.assertEqual(len(lint_statement('(x y : ℝ) : x ^ (2 / 3) * y ^ (1/3) ≥ 0')), 1)
        self.assertEqual(lint_statement('(x : ℝ) : x ^ ((1 : ℝ) / 3) ≥ 0'), [])
        self.assertEqual(lint_statement('(n : ℕ) : n ^ 2 / 3 ≤ n ^ 2'), [])

    def test_disproof_is_inferred_from_the_declared_name(self):
        from forge.statement import is_disproof
        self.assertTrue(is_disproof('theorem foo_disproof : ¬ False := id\n', 'foo'))
        self.assertFalse(is_disproof('theorem foo : True := trivial\n', 'foo'))
        self.assertFalse(is_disproof('-- theorem foo_disproof\ntheorem foo : True := trivial\n', 'foo'))
        self.assertFalse(is_disproof('theorem foo_disproof_aux : True := trivial\n', 'foo'))

    def test_sketch_allows_only_sorry(self):
        body = 'theorem foo : True := by\n  sorry\n'
        self.assertEqual(analyse_submission(body, 'foo', allow_holes=True), ['foo'])
        with self.assertRaises(StatementError):
            analyse_submission('axiom c : False\n' + body, 'foo', allow_holes=True)


class QueueTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.patch = mock.patch.object(tasks, 'TASKS', Path(self.tmp.name) / 'tasks')
        self.patch.start()

    def tearDown(self):
        self.patch.stop()
        self.tmp.cleanup()

    def _task(self, name, attempts=0):
        tasks.save('open', dict(name=name, statement=': True', attempts=[{}] * attempts, created_at='t', status='open'))

    def test_claim_is_exclusive_under_concurrency(self):
        for i in range(6):
            self._task(f'task{i}')
        claimed = []

        def worker(k):
            for _ in range(6):
                task = tasks.claim(f'agent{k}')
                if task:
                    claimed.append(task['name'])

        threads = [threading.Thread(target=worker, args=(k,)) for k in range(8)]
        [t.start() for t in threads]
        [t.join() for t in threads]
        self.assertEqual(sorted(claimed), [f'task{i}' for i in range(6)])  # 每个任务恰好被领一次
        self.assertIsNone(tasks.claim('late'))

    def test_release_records_the_failed_attempt_and_deprioritises(self):
        self._task('alpha')
        self._task('beta')
        first = tasks.claim('a1')
        self.assertTrue(tasks.release(first['name'], 'a1', '试过归纳，卡在归纳步')['ok'])
        self.assertNotEqual(tasks.claim('a2')['name'], first['name'])  # 没人试过的优先
        again = tasks.claim('a3')
        self.assertEqual(again['name'], first['name'])
        self.assertEqual(again['attempts'][0]['note'], '试过归纳，卡在归纳步')

    def test_only_the_claimant_can_release_or_retire(self):
        self._task('alpha')
        tasks.claim('owner')
        self.assertFalse(tasks.release('alpha', 'intruder', 'x')['ok'])
        self.assertFalse(tasks.retire('alpha', 'intruder', 'x')['ok'])
        self.assertIn('owner', tasks.submit('alpha', 'theorem alpha : True := trivial\n', 'intruder')['reason'])
        self.assertTrue(tasks.retire('alpha', 'owner', '命题有误')['ok'])
        self.assertEqual(tasks.load('alpha')[1]['status'], 'retired')

    def test_prefix_filter_and_queue_listing(self):
        self._task('ab_one')
        self._task('r3_one')
        self.assertEqual(tasks.claim('a', prefix='r3_')['name'], 'r3_one')
        self.assertIsNone(tasks.claim('b', prefix='r3_'))
        listing = {row['name']: row for row in tasks.queue()}
        self.assertEqual(listing['r3_one']['claimed_by'], 'a')
        self.assertEqual(listing['ab_one']['state'], 'open')

    def test_assemble_reports_a_dead_sketch(self):
        tasks.save('done', dict(name='kid', statement=': True', attempts=[], created_at='a', status='disproved'))
        tasks.save('open', dict(name='parent', statement=': True', attempts=[], created_at='a', status='open',
                                sketches=[dict(body='x', children=[dict(task='kid')])]))
        result = tasks.assemble('parent', 'a')
        self.assertFalse(result['ok'])
        self.assertIn('作废', result['reason'])

    def test_parent_waits_for_sketch_children(self):
        self._task('child')
        tasks.save('open', dict(name='parent', statement=': True', attempts=[], created_at='a', status='open',
                                sketches=[dict(children=[dict(task='child')])]))
        self.assertEqual(tasks.claim('a')['name'], 'child')
        self.assertIsNone(tasks.claim('b'))  # 子任务还在进行，父任务不发出


class InsightTests(unittest.TestCase):
    ENTRIES = [
        dict(name='base', task='base', kind='proved', tier='agent', type='∀ (a b : ℕ), a ∣ b → 0 < b → a ≤ b',
             informal='正数的因子不超过它', library_deps=[], attempts=1),
        dict(name='mid', task='mid', kind='proved', tier='auto', type='∀ (n : ℕ), n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1',
             informal='平方数模 4', library_deps=['base'], attempts=1),
        dict(name='top', task='top', kind='proved', tier='agent', type='∀ (n : ℕ), ∑ i ∈ Finset.range n, i = n',
             informal='', library_deps=['mid', 'base'], attempts=3),
    ]

    HELPERS = {'base_aux1': dict(owner='base', type='∀ (c : ℚ) (M : Matrix (Fin 2) (Fin 2) ℚ), c ≠ 0 → (c • M).rank = M.rank', hash='1')}

    def setUp(self):
        self.patch = mock.patch('forge.library.entries', return_value=self.ENTRIES)
        self.helpers = mock.patch('forge.library.helper_index', return_value=self.HELPERS)
        self.patch.start()
        self.helpers.start()

    def tearDown(self):
        self.patch.stop()
        self.helpers.stop()

    def test_helpers_are_found_by_statement_not_by_name(self):
        hit = insight.search('rank • smul')[0]
        self.assertEqual(hit['name'], 'Mathlib2.base_aux1')
        self.assertEqual(hit['tier'], 'helper')

    def test_dag_depth_and_edges_come_from_recorded_dependencies(self):
        graph = insight.dag('top')
        self.assertEqual({n['name']: n['depth'] for n in graph['nodes']}, {'base': 0, 'mid': 1, 'top': 2})
        self.assertEqual(len(graph['edges']), 3)
        self.assertEqual([n['name'] for n in insight.dag('mid')['nodes']], ['base', 'mid'])

    def test_search_matches_symbols_and_words(self):
        self.assertEqual(insight.search('∣ ≤')[0]['name'], 'Mathlib2.base')
        self.assertEqual(insight.search('range sum ∑')[0]['name'], 'Mathlib2.top')
        self.assertEqual(insight.search('zzz'), [])

    def test_report_prefers_cited_agent_level_results(self):
        self.assertEqual([r['name'] for r in insight.report()], ['base', 'top', 'mid'])


@unittest.skipUnless(os.environ.get('FORGE_INTEGRATION') == '1', '需要真实 Lean/Mathlib；设置 FORGE_INTEGRATION=1')
class KernelTests(unittest.TestCase):
    """只调用校验与分诊（不入库、不动队列），确认裁判真的在内核一侧。"""
    TASK = dict(name='itest_succ', statement='(n : ℕ) : n + 1 = n')

    def test_disproof_accepted_and_wrong_statement_rejected(self):
        from forge.verify import check_submission
        good = 'theorem itest_succ_disproof : ¬ (∀ (n : ℕ), n + 1 = n) := by\n  intro h\n  have := h 0\n  omega\n'
        result = check_submission(self.TASK, good, disproof=True)
        self.assertTrue(result['ok'], result)
        self.assertLessEqual(set(result['axioms']), {'propext', 'Classical.choice', 'Quot.sound'})
        other = good.replace('n + 1 = n', 'n + 2 = n')
        self.assertIn('不一致', check_submission(self.TASK, other, disproof=True)['reason'])

    def test_errors_are_reported_with_relative_lines(self):
        from forge.verify import check_submission
        task = dict(name='itest_refl', statement='(n : ℕ) : n = n')
        bad = 'theorem itest_refl (n : ℕ) : n = n := by\n  exact no_such_lemma n\n'
        result = check_submission(task, bad)
        self.assertFalse(result['ok'])
        self.assertEqual(result['errors'][0]['line'], 2)

    def test_triage_separates_known_refuted_and_open(self):
        from forge.verify import triage
        known = triage('itest_known', '(a b : ℕ) (h : a ∣ b) (hb : 0 < b) : a ≤ b')
        self.assertTrue(known['known'])
        self.assertIn('Nat.le_of_dvd', known['known_as'])
        refuted = triage('itest_false', '(n : ℕ) : n + 1 = n')
        self.assertIn('counter-example', refuted['counterexample'])
        self.assertFalse(refuted.get('known'))
        self.assertFalse(triage('itest_bad', '(n : ℕ) : n +')['valid'])
        # 缺实例的命题会被 Lean 记成类型里带 sorry 的常量，必须判为无效
        ill = triage('itest_illtyped', '{k : Type*} [Field k] (a : Polynomial k) : 1 ≤ (UniqueFactorizationMonoid.radical a).natDegree')
        self.assertFalse(ill['valid'])
        self.assertTrue(ill['errors'])

    def test_sketch_extracts_closed_goals_from_the_kernel(self):
        from forge.verify import check_sketch
        task = dict(name='itest_sq', statement='(n : ℕ) : n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1')
        body = ('theorem itest_sq (n : ℕ) : n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1 := by\n'
                '  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩\n  · left\n    sorry\n  · right\n    sorry\n')
        result = check_sketch(task, body)
        self.assertTrue(result['ok'], result)
        self.assertEqual([h['statement'] for h in result['holes']],
                         ['∀ (n k : ℕ), n = k + k → n ^ 2 % 4 = 0', '∀ (n k : ℕ), n = 2 * k + 1 → n ^ 2 % 4 = 1'])


    def test_sketch_rejects_holes_that_do_not_round_trip(self):
        # 置换乘积作用于 x：打印后再解析会被读成逐点乘积，含义变了，必须在登记前拦下
        from forge.verify import check_sketch
        task = dict(name='itest_perm', statement='(n : ℕ) (τ ρ : Equiv.Perm (Fin n)) (x : Fin n) (h : (τ * ρ) x = x) : ρ x = τ⁻¹ x')
        body = ('theorem itest_perm (n : ℕ) (τ ρ : Equiv.Perm (Fin n)) (x : Fin n) (h : (τ * ρ) x = x) : ρ x = τ⁻¹ x := by\n'
                '  have key : ρ x = τ⁻¹ x := by\n    sorry\n  exact key\n')
        result = check_sketch(task, body)
        self.assertFalse(result['ok'])
        self.assertIn('不是原来的命题', result['reason'])

    def test_one_sorry_may_cover_several_goals(self):
        from forge.verify import check_sketch
        task = dict(name='itest_conj', statement='(n : ℕ) : n ≤ n * n + n ∧ n + 0 = n')
        body = ('theorem itest_conj (n : ℕ) : n ≤ n * n + n ∧ n + 0 = n := by\n'
                '  refine ⟨?_, ?_⟩ <;> sorry\n')
        result = check_sketch(task, body)
        self.assertTrue(result['ok'], result)
        self.assertEqual(len(result['holes']), 2)
        self.assertEqual(result['holes'][0]['args'], ['n'])

    def test_triage_flags_vacuous_hypotheses_but_not_negations(self):
        from forge.verify import triage
        vacuous = triage('itest_vac', '(n : ℕ) (h1 : n < 3) (h2 : 5 < n) : Nat.Prime n')
        self.assertTrue(vacuous.get('vacuous'))
        # 结论是否定（¬P 即 P → False）时不能被当成空真
        negation = triage('itest_neg', '(n : ℕ) (h : 2 ≤ n) : ¬ (n ^ 2 = 2)')
        self.assertFalse(negation.get('vacuous'))

    def test_incident_regressions_all_pass(self):
        # 事故回归集：每次出过的问题都是一条用例（forge/data/regressions.jsonl）
        from forge.regressions import run
        result = run(jobs=3)
        self.assertTrue(result['ok'], [r for r in result['results'] if not r['ok']])

    def test_unbound_names_are_errors_not_new_variables(self):
        # 自动隐式变量会把写错的名字悄悄变成任意变量，从而改变题意；所有检查都必须把它当错误
        from forge.verify import statement_hashes, triage
        self.assertFalse(triage('itest_unbound', '(n : ℕ) : n + k = k + n')['valid'])
        self.assertEqual(statement_hashes(['(n : ℕ) : (∏ k ∈ Finset.range n, 1) + k = 1 + k'])[0], None)

    def test_statement_hashes_match_triage(self):
        from forge.verify import statement_hashes, triage
        statement = '(a b : ℕ) (h : a ∣ b) : a ∣ b * 7'
        self.assertEqual(statement_hashes([statement, '(n : ℕ) : n +']), [triage('itest_hash', statement)['hash'], None])


class HardeningTests(unittest.TestCase):
    """组提交、评测集保护与成绩、分诊里空真/一步推论结论的解析：都不需要 Lean。"""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)

    def tearDown(self):
        self.tmp.cleanup()

    def test_batch_build_failure_falls_back_to_one_by_one(self):
        from forge import library
        calls = []

        def fake_admit_batch(items, _real=library.admit_batch):
            calls.append(len(items))
            return _real(items)

        # 合并构建失败、回滚后重建、t0 单独构建成功、t1 单独构建失败、回滚后重建
        builds = iter([(1, 'error: duplicate'), (0, ''), (0, ''), (1, 'error'), (0, '')])
        with mock.patch.object(library, 'SHARDS', self.root / 'Shard'), \
                mock.patch.object(library, 'ROOT_FILE', self.root / 'Mathlib2.lean'), \
                mock.patch.object(library, 'LEDGER', self.root / 'ledger.jsonl'), \
                mock.patch.object(library, 'lake_build', side_effect=lambda target: next(builds)), \
                mock.patch.object(library, 'admit_batch', side_effect=fake_admit_batch):
            (self.root / 'Mathlib2.lean').write_text('import Mathlib\n', encoding='utf-8')
            check = dict(kind='proved', type='True', axioms=[], library_deps=[], external_deps=0, names=['x'])
            items = [(dict(name=f't{i}', statement=': True'), f'theorem t{i} : True := trivial\n', dict(check, names=[f't{i}']), 'a')
                     for i in range(2)]
            results = library.admit_batch(items)
        # 第一次合并构建失败 → 回滚 → 逐条：t0 构建成功；t1 构建失败再回滚
        self.assertEqual([r['ok'] for r in results], [True, False])
        self.assertEqual(calls, [2, 1, 1])  # 先整批，再逐条
        ledger = (self.root / 'ledger.jsonl').read_text(encoding='utf-8')
        self.assertIn('"t0"', ledger)
        self.assertNotIn('"t1"', ledger)
        shard = (self.root / 'Shard' / 'S0001.lean').read_text(encoding='utf-8')
        self.assertIn('theorem t0', shard)
        self.assertNotIn('theorem t1', shard)

    def test_concurrent_commits_share_one_build(self):
        from forge import library
        builds = []
        gate = threading.Event()

        def slow_build(target):
            builds.append(target)
            gate.wait(2)  # 第一次构建期间其余提交排进待入库区
            return 0, ''

        with mock.patch.object(library, 'SHARDS', self.root / 'Shard'), \
                mock.patch.object(library, 'ROOT_FILE', self.root / 'Mathlib2.lean'), \
                mock.patch.object(library, 'LEDGER', self.root / 'ledger.jsonl'), \
                mock.patch.object(library, 'LOCK', self.root / 'lock'), \
                mock.patch.object(library, 'PENDING', self.root / 'pending'), \
                mock.patch.object(library, 'lake_build', side_effect=slow_build):
            (self.root / 'Mathlib2.lean').write_text('import Mathlib\n', encoding='utf-8')
            check = dict(kind='proved', type='True', axioms=[], library_deps=[], external_deps=0)
            results = {}

            def submit(i):
                results[i] = library.commit(dict(name=f'c{i}', statement=': True'), f'theorem c{i} : True := trivial\n',
                                            dict(check, names=[f'c{i}']), 'a')

            first = threading.Thread(target=submit, args=(0,))
            first.start()
            while not builds:
                pass
            others = [threading.Thread(target=submit, args=(i,)) for i in range(1, 4)]
            for t in others:
                t.start()
            import time as _time
            _time.sleep(0.5)
            gate.set()
            for t in [first] + others:
                t.join()
        self.assertTrue(all(r['ok'] for r in results.values()))
        self.assertEqual(len(builds), 2)  # 第一条单独一次，后面三条合并成一次
        self.assertEqual(sorted(r['batch'] for r in results.values()), [1, 3, 3, 3])
        self.assertFalse(list((self.root / 'pending').iterdir()))

    def test_bench_reserves_statements_and_scores_runs(self):
        from forge import bench
        with mock.patch.object(bench, 'BENCH', self.root / 'bench'), mock.patch.object(bench, 'RUNS', self.root / 'bench' / 'runs'), \
                mock.patch.object(bench, 'statement_hashes', return_value=['h1', None]):
            source = self.root / 'in.jsonl'
            source.write_text('{"name": "p1", "statement": "(n : ℕ) : n = n"}\n{"name": "p2", "statement": "bad"}\n', encoding='utf-8')
            # p2 的命题格式本身不合法（没有 `binders : conclusion`），在求哈希之前就被剔出
            self.assertEqual(bench.import_set('demo', source), dict(set='demo', imported=1, dropped=[], unfaithful=[], unusable=['p2']))
            self.assertEqual(bench.reserved(), {'h1': 'demo/p1'})
            verdicts = iter([dict(ok=False, kind='proved', reason='Lean 报错'), dict(ok=True, kind='proved', reason='通过')])
            with mock.patch.object(bench, 'check_submission', side_effect=lambda *a, **k: next(verdicts)):
                self.assertFalse(bench.check('demo', 'p1', 'x', 'r1', 'a')['solved'])
                self.assertTrue(bench.check('demo', 'p1', 'y', 'r2', 'a')['solved'])
            runs = {r['run']: r for r in bench.score('demo')['runs']}
            self.assertEqual((runs['r1']['solved'], runs['r2']['solved'], runs['r2']['rate']), (0, 1, 1.0))
            with self.assertRaises(ValueError):
                bench.load('../escape')

    def test_triage_reports_vacuity_and_one_step_corollaries(self):
        from forge import verify
        ran = {}

        def fake_ladder(decl, labelled, timeout, named=False):
            labels = {label for label, _, _ in labelled}
            ran.setdefault('labels', set()).update(labels)
            passed = {l for l in labels if l in ('vac:omega', 'lib:0:grind [Mathlib2.a]', 'lib:1:simp_all [Mathlib2.b]')}
            if not named:
                return passed, {}, False
            # a 的探针虽然成功，但证明里没有引用 a；b 的探针确实引用了 b
            deps = {'lib:0:grind [Mathlib2.a]': {'Nat.add_comm'}, 'lib:1:simp_all [Mathlib2.b]': {'Mathlib2.b'}}
            return passed, {}, False, deps

        fake = mock.MagicMock()
        fake.tagged.return_value = [dict(type='T', hash='h')]
        fake.errors.return_value = []
        fake.elapsed, fake.timed_out = 1.0, False
        with mock.patch.object(verify, '_ladder_run', side_effect=fake_ladder), \
                mock.patch.object(verify, 'run_source', return_value=fake), \
                mock.patch('forge.insight.search', return_value=[dict(name='Mathlib2.a'), dict(name='Mathlib2.b')]):
            out = verify.triage('t', '(n : ℕ) (h : n < 0) : n = 1')
            self.assertEqual(out['vacuous'], 'omega')
            self.assertEqual(out['follows_from'], dict(lemma='Mathlib2.b', tactic='simp_all [Mathlib2.b]'))
            # 没有签名假设时不做空真检查
            ran.clear()
            verify.triage('t', ': 1 = 1')
            self.assertFalse(any(l.startswith('vac:') for l in ran['labels']))


class ImporterTests(unittest.TestCase):
    def test_big_operator_bodies_keep_their_old_scope(self):
        from forge.importers import convert_big_operators
        cases = {
            '(∏ k in Finset.Icc 1 n, 1 + (1 : ℝ) / 2 ^ k) < 5 / 2': '(∏ k ∈ Finset.Icc 1 n, (1 + (1 : ℝ) / 2 ^ k)) < 5 / 2',
            '¬5 ∣ ∑ k in Finset.range (n + 1), f k * 2': '¬5 ∣ ∑ k ∈ Finset.range (n + 1), (f k * 2)',
            '∑ k : ℤ in Finset.Icc 1 12, z ^ k = 0': '∑ k ∈ (Finset.Icc 1 12 : Finset ℤ), (z ^ k = 0)',
            '(∑ i in s, ∑ j in t, a i j) = 0': '(∑ i ∈ s, (∑ j ∈ t, (a i j))) = 0',
            '∑ x ∈ s, f x = 1': '∑ x ∈ s, f x = 1',  # 已经是新写法的不动
        }
        for old, new in cases.items():
            self.assertEqual(convert_big_operators(old)[0], new, old)

    def test_theorem_signature_extraction(self):
        from forge.importers import theorem_signature
        self.assertEqual(theorem_signature('theorem lw_1 (a b : ℝ) (h : 0 < a) :\n  a + b > b  :=  by sorry'),
                         ('lw_1', '(a b : ℝ) (h : 0 < a) : a + b > b'))
        self.assertEqual(theorem_signature('/-- doc -/\ntheorem t : 1 = 1 := sorry'), ('t', ': 1 = 1'))
        self.assertIsNone(theorem_signature('def f := 1\ntheorem t : f = 1 := sorry'))
        self.assertIsNone(theorem_signature('theorem t : 1 = 1 := rfl'))


class PutnamImportTests(unittest.TestCase):
    def test_answer_is_filled_from_the_comment(self):
        from forge.importers import putnam_problem
        src = ('import Mathlib\n\nopen Nat\n\ndef helper : ℕ → ℕ\n| 0 => 0\n| (n+1) => helper n + 1\n'
               'abbrev putnam_x_solution : ℕ → ℕ := sorry\n-- fun n : ℕ => n * 2\n/--\nEvaluate.\n-/\n'
               'theorem putnam_x\n: ∀ n, putnam_x_solution n = helper n * 2 :=\nsorry\n')
        item = putnam_problem(src)
        self.assertEqual(item['name'], 'putnam_x')
        self.assertEqual(item['statement'], ': ∀ n, putnam_x_solution n = helper n * 2')
        self.assertEqual(item['opens'], 'Nat')
        self.assertIn('abbrev putnam_x_solution : ℕ → ℕ := fun n : ℕ => n * 2', item['preamble'])
        self.assertIn('def helper', item['preamble'])
        self.assertNotIn('sorry', item['preamble'])

    def test_problems_without_an_answer_or_preamble(self):
        from forge.importers import putnam_problem
        item = putnam_problem('import Mathlib\n/-- text -/\ntheorem putnam_y (x : ℝ) : x = x :=\nsorry\n')
        self.assertEqual(item, dict(name='putnam_y', statement='(x : ℝ) : x = x'))
        self.assertIsNone(putnam_problem('import Mathlib\nabbrev putnam_z_solution : ℕ := sorry\ntheorem putnam_z : putnam_z_solution = 1 := sorry\n'))


class FormalConjecturesImportTests(unittest.TestCase):
    SOURCE = ('/-\nCopyright\n-/\nmodule\n\npublic import FormalConjecturesUtil\n\n@[expose] public section\n\n'
              'open Filter\nopen scoped Topology\n\nnamespace Erdos9\n\ndef good (n : ℕ) : Prop := n = n\n\n'
              '/-- Solved. -/\n@[category research solved, AMS 11]\ntheorem erdos_9 (n : ℕ) : good n := by\n  sorry\n\n'
              '@[category research solved, AMS 11, formal_proof using lean4 at "https://x"]\n'
              'theorem erdos_9.variants.known : good 1 := by\n  sorry\n\n'
              '@[category research open, AMS 11]\ntheorem erdos_9.variants.open : good 2 := by\n  sorry\n\n'
              '@[category test, AMS 11]\ntheorem erdos_9.test : good 3 := by\n  rfl\n\nend Erdos9\n')

    def extract(self, **kwargs):
        from forge.importers import formal_conjectures_problems
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'FormalConjectures' / 'ErdosProblems' / '9.lean'
            path.parent.mkdir(parents=True)
            path.write_text(self.SOURCE, encoding='utf-8')
            return formal_conjectures_problems(tmp, **kwargs)

    def test_public_section_does_not_hide_the_namespace(self):
        items = self.extract()
        self.assertEqual(len(items), 1)  # 带公开 Lean 证明的、开放的、测试用的都不收
        item = items[0]
        self.assertEqual(item['origin'], 'Erdos9.erdos_9')
        self.assertEqual(item['statement'], '(n : ℕ) : good n')
        self.assertEqual(item['imports'], ['FormalConjectures.ErdosProblems.«9»'])
        self.assertEqual(item['preamble'], 'open Filter\nopen scoped Topology\nopen Erdos9')

    def test_category_and_public_proof_filters(self):
        names = {i['origin'] for i in self.extract(categories=('research solved', 'research open'), skip_public_proof=False)}
        self.assertEqual(names, {'Erdos9.erdos_9', 'Erdos9.erdos_9.variants.known', 'Erdos9.erdos_9.variants.open'})

    def test_extra_imports_go_after_the_fixed_ones_and_are_validated(self):
        from forge.verify import HEADER, header
        self.assertEqual(header(), HEADER)
        text = header(['FormalConjectures.ErdosProblems.«9»'])
        self.assertTrue(text.startswith('import Mathlib\nimport Mathlib2\nimport Forge\nimport FormalConjectures.ErdosProblems.«9»\nset_option'))
        with self.assertRaises(ValueError):
            header(['Foo\n#eval 1'])


class BenchMidBuildTests(unittest.TestCase):
    def test_missing_olean_is_rechecked_under_the_lock(self):
        from forge import bench
        broken = dict(ok=False, kind='proved', reason='Lean 报错',
                      errors=[dict(line=0, column=0, message="object file '/x/Mathlib2.olean' of module Mathlib2 does not exist")])
        good = dict(ok=True, kind='proved', reason='通过：命题匹配，公理合规')
        with tempfile.TemporaryDirectory() as tmp, \
                mock.patch.object(bench, 'load', return_value=[dict(name='p', statement=': True')]), \
                mock.patch.object(bench, 'RUNS', Path(tmp)), \
                mock.patch('forge.library.LOCK', Path(tmp) / 'lock'), \
                mock.patch.object(bench, 'check_submission', side_effect=[broken, good]) as checker:
            self.assertTrue(bench.check('demo', 'p', 'proof', 'r', 'a')['solved'])
            self.assertEqual(checker.call_count, 2)


class UpgradeRepairTests(unittest.TestCase):
    BEFORE = ('-- forge:entry foo kind=proved origin=x\nsection\n'
              'lemma foo_aux1 (n : ℕ) : n + 0 = n := by\n  simp\n'
              'theorem foo (a b : ℕ) (h : a ≤ b) : a ≤ b + 1 := by\n  omega\nend\n')

    def test_proof_only_changes_are_accepted(self):
        from forge.upgrade import check_repair
        after = self.BEFORE.replace('  simp\n', '  exact Nat.add_zero n\n')
        self.assertEqual(check_repair(self.BEFORE, after), [])

    def test_stub_replaces_only_the_broken_proof(self):
        from forge.upgrade import stub_declarations, signatures
        text = ('-- forge:entry foo kind=proved origin=x\nsection\n'
                'lemma foo_aux1 (n : ℕ) : n + 0 = n := by\n  simp\n'          # 第 3–4 行
                'theorem foo (a b : ℕ) (h : a ≤ b) : a ≤ b + 1 := by\n  old_tactic\n  omega\nend\n')  # 第 5–7 行
        stubbed, names = stub_declarations(text, [6])
        self.assertEqual(names, ['foo'])
        self.assertIn('lemma foo_aux1 (n : ℕ) : n + 0 = n := by\n  simp\n', stubbed)   # 没报错的证明不动
        self.assertIn(':= by\n  sorry', stubbed)
        self.assertNotIn('old_tactic', stubbed)
        self.assertEqual(signatures(stubbed), signatures(text))                      # 陈述完全不变
        self.assertTrue(stubbed.rstrip().endswith('end'))
        # 报错在陈述里（`:=` 之前）：打桩救不了，原样返回
        self.assertEqual(stub_declarations(text, [5]), (text, []))

    def test_reviewed_migration_is_applied_to_statements(self):
        from forge.upgrade import migrate
        new, used = migrate('theorem t {M : Type*} [CancelCommMonoidWithZero M] (x : M) : x = x := rfl')
        self.assertIn('[CommMonoidWithZero M] [IsCancelMulZero M]', new)
        self.assertEqual(len(used), 1)
        self.assertEqual(migrate('theorem t : 1 = 1 := rfl'), ('theorem t : 1 = 1 := rfl', []))

    def test_statement_changes_and_cheats_are_rejected(self):
        from forge.upgrade import check_repair
        weakened = self.BEFORE.replace('a ≤ b + 1', 'a ≤ b + 2')
        self.assertIn('`foo` 的陈述被改动', check_repair(self.BEFORE, weakened))
        cheat = self.BEFORE.replace('  omega\n', '  sorry\n')
        self.assertTrue(any('sorry' in p for p in check_repair(self.BEFORE, cheat)))
        extra = self.BEFORE + 'theorem foo_aux2 : True := trivial\n'
        self.assertTrue(any('声明集合' in p for p in check_repair(self.BEFORE, extra)))
        renamed_marker = self.BEFORE.replace('kind=proved', 'kind=disproved')
        self.assertIn('条目标记被改动', check_repair(self.BEFORE, renamed_marker))


class SchedulerTests(unittest.TestCase):
    """调度器的控制逻辑：不调用真实 agent，也不碰真实队列。"""

    def setUp(self):
        from forge import scheduler
        self.tmp = tempfile.TemporaryDirectory()
        root = Path(self.tmp.name)
        self.patches = [mock.patch.object(scheduler, 'RUNS', root / 'runs'), mock.patch.object(scheduler, 'DATA', root)]
        for p in self.patches:
            p.start()
        self.scheduler = scheduler

    def tearDown(self):
        for p in self.patches:
            p.stop()
        self.tmp.cleanup()

    def test_invoke_creates_its_scratch_directory(self):
        # 事故：并行修复给每个分片建了新的调度器，临时目录不存在，Codex 写不了最后一条消息就直接退出
        s = self.scheduler.Scheduler('fresh-dir', workers=1, agent_cmd='true')
        self.assertFalse(s.scratch.exists())
        code, _, _, _ = s._invoke('hello', 'worker')
        self.assertEqual(code, 0)
        self.assertTrue(s.scratch.is_dir())

    def test_token_count_is_read_from_agent_output(self):
        self.assertEqual(self.scheduler._tokens('...\ntokens used\n18,291\n684'), 18291)
        self.assertIsNone(self.scheduler._tokens('no usage here'))

    def test_unfinished_tasks_are_released_and_the_breaker_trips(self):
        s = self.scheduler.Scheduler('t1', workers=1, max_tasks=10, max_failures=2)
        queue = [dict(name=f'g{i}', statement=': True', attempts=[]) for i in range(5)]
        claimed = {}
        released = []

        def claim(agent, prefix=None, parity=None):
            if not queue:
                return None
            task = queue.pop(0)
            claimed[task['name']] = agent
            return task

        with mock.patch.object(s, '_invoke', return_value=(0, 'RESULT: released', 1000, False)), \
                mock.patch('forge.tasks.claim', side_effect=claim), \
                mock.patch('forge.tasks.load', side_effect=lambda n: ('claimed', dict(name=n, claimed_by=claimed[n]))), \
                mock.patch('forge.tasks.release', side_effect=lambda n, a, note: released.append(n)):
            summary = s.run_queue()
        self.assertEqual(released, ['g0', 'g1'])  # 两次没有进展就熔断，没有再领第三道
        self.assertEqual(summary['outcomes'], {'released_by_scheduler': 2})
        self.assertEqual(summary['tokens'], 2000)
        self.assertIn('熔断', summary['stopped'])

    def test_proved_tasks_count_as_progress(self):
        s = self.scheduler.Scheduler('t2', workers=1, max_tasks=2, max_failures=1)
        queue = [dict(name='g0', statement=': True', attempts=[]), dict(name='g1', statement=': True', attempts=[])]
        with mock.patch.object(s, '_invoke', return_value=(0, 'RESULT: proved', None, False)), \
                mock.patch('forge.tasks.claim', side_effect=lambda agent, prefix=None, parity=None: queue.pop(0) if queue else None), \
                mock.patch('forge.tasks.load', side_effect=lambda n: ('done', dict(name=n, status='proved', closed_by='t2-w0'))):
            summary = s.run_queue()
        self.assertEqual(summary['outcomes'], {'proved': 2})
        self.assertEqual(summary['stopped'], '任务数用完')

    def test_bench_score_comes_from_the_schedulers_own_check(self):
        s = self.scheduler.Scheduler('b1', workers=1, max_tasks=5, max_failures=5)
        items = [dict(name='p1', statement=': True'), dict(name='p2', statement=': True')]
        checked = []

        def fake_invoke(prompt, worker):
            if 'p1' in prompt.split('Problem name:')[1][:10]:  # agent 只为 p1 交了证明文件；p2 只声称做出来了
                (s.scratch / worker / 'p1.lean').write_text('theorem p1 : True := trivial\n', encoding='utf-8')
            return 0, 'RESULT: solved', 10, False

        def fake_check(set_name, problem, body, run, agent):
            checked.append((problem, agent))
            return dict(ok=True, kind='proved', solved=True, reason='通过')

        with mock.patch.object(s, '_invoke', side_effect=fake_invoke), \
                mock.patch('forge.bench.load', return_value=items), mock.patch('forge.bench.check', side_effect=fake_check):
            summary = s.run_bench('demo', only_unsolved=False)
        self.assertEqual(checked, [('p1', 'scheduler')])
        self.assertEqual(summary['outcomes'], {'solved': 1, 'unsolved': 1})

    def test_shards_split_the_benchmark_without_overlap(self):
        items = [dict(name=f'p{i}', statement=': True') for i in range(7)]
        seen = []
        for k in (1, 2):
            s = self.scheduler.Scheduler(f's{k}@m{k}', workers=1, max_tasks=99, max_failures=99)
            prompts = []
            with mock.patch.object(s, '_invoke', side_effect=lambda prompt, worker: (prompts.append(prompt), (0, '', 0, False))[1]), \
                    mock.patch('forge.bench.load', return_value=items):
                s.run_bench('demo', only_unsolved=False, shard=(k, 2))
            names = [p.split('Problem name: ')[1].split('\n')[0] for p in prompts]
            self.assertTrue(all(self.scheduler.FORGE in p for p in prompts))  # 提示词里是本平台的 forge 命令
            seen.append(names)
        self.assertEqual(sorted(seen[0] + seen[1]), sorted(i['name'] for i in items))
        self.assertFalse(set(seen[0]) & set(seen[1]))

    def test_bench_prompt_shows_the_fixed_preamble(self):
        s = self.scheduler.Scheduler('pre', workers=1, max_tasks=5, max_failures=5)
        items = [dict(name='px', statement=': px_solution = 1', preamble='abbrev px_solution : ℕ := 1')]
        prompts = []
        with mock.patch.object(s, '_invoke', side_effect=lambda prompt, worker: (prompts.append(prompt), (0, '', 0, False))[1]), \
                mock.patch('forge.bench.load', return_value=items):
            s.run_bench('demo', only_unsolved=False)
        self.assertIn('abbrev px_solution : ℕ := 1', prompts[0])

    def test_bench_prompt_points_to_the_imported_source(self):
        s = self.scheduler.Scheduler('src', workers=1, max_tasks=5, max_failures=5)
        items = [dict(name='fc_x', statement='(n : ℕ) : good n', imports=['FormalConjectures.ErdosProblems.«9»'],
                      source='FormalConjectures/ErdosProblems/9.lean', preamble='open Erdos9')]
        prompts = []
        with mock.patch.object(s, '_invoke', side_effect=lambda prompt, worker: (prompts.append(prompt), (0, '', 0, False))[1]), \
                mock.patch('forge.bench.load', return_value=items):
            s.run_bench('demo', only_unsolved=False)
        self.assertIn('FormalConjectures.ErdosProblems.«9»', prompts[0])
        self.assertIn('formal_conjectures/FormalConjectures/ErdosProblems/9.lean', prompts[0])
        self.assertIn('sorryAx', prompts[0])

    def test_ladder_escalates_only_when_unsolved_and_passes_the_draft_on(self):
        s = self.scheduler.Scheduler('lad', workers=1, max_tasks=5, max_failures=5, ladder=[('low', 5), ('xhigh', 30)])
        items = [dict(name='easy', statement=': True'), dict(name='hard', statement=': True')]
        calls = []

        def fake_invoke(prompt, worker, effort=None, seconds=None):
            name = prompt.split('Problem name: ')[1].split('\n')[0]
            calls.append((name, effort, seconds, 'previous attempt' in prompt))
            (s.scratch / worker / f'{name}.lean').write_text(f'-- {name} by {effort}\n', encoding='utf-8')
            return 0, f'RESULT from {effort}', 5, False

        # easy 第一次就做出来；hard 第一档没做出、第二档做出
        verdicts = {('easy', 1): True, ('hard', 1): False, ('hard', 2): True}
        attempts = {}

        def fake_check(set_name, problem, body, run, agent):
            attempts[problem] = attempts.get(problem, 0) + 1
            return dict(ok=True, kind='proved', solved=verdicts[(problem, attempts[problem])], reason='r')

        with mock.patch.object(s, '_invoke', side_effect=fake_invoke), \
                mock.patch('forge.bench.load', return_value=items), mock.patch('forge.bench.check', side_effect=fake_check):
            summary = s.run_bench('demo', only_unsolved=False)
        self.assertEqual(calls, [('easy', 'low', 300, False), ('hard', 'low', 300, False), ('hard', 'xhigh', 1800, True)])
        self.assertEqual(summary['outcomes'], {'solved': 2, 'unsolved': 1})
        draft = s.scratch / 'lad-w0' / 'hard.attempt1.lean'
        self.assertEqual(draft.read_text(encoding='utf-8'), '-- hard by low\n')

    def test_review_mode_only_reviews_settled_unreviewed_items(self):
        root = Path(self.tmp.name)
        paper = dict(title='T', arxiv='0000.00000', statements=[
            dict(label='Thm 1', name='q_done', lean=': True', original='o'),
            dict(label='Thm 2', name='q_open', lean=': True', original='o'),
            dict(label='Thm 3', name='q_reviewed', lean=': True', original='o'),
            dict(label='Thm 4', name='q_disproved', lean=': False', original='o')])
        (root / 'paper.json').write_text(json.dumps(paper), encoding='utf-8')
        (root / 'paper.txt').write_text('full text', encoding='utf-8')
        states = {'q_done': ('done', dict(status='proved', closed_by='prover')), 'q_open': ('open', dict(status='open')),
                  'q_reviewed': ('done', dict(status='proved', closed_by='prover')),
                  'q_disproved': ('done', dict(status='disproved', closed_by='prover'))}
        recorded = {'q_reviewed': [dict(agent='someone_else', verdict='faithful')]}
        s = self.scheduler.Scheduler('rv', workers=1, max_tasks=10, max_failures=10)
        prompts = []

        def fake_invoke(prompt, worker):
            prompts.append(prompt)
            name = prompt.split('Lean task name: ')[1].split('\n')[0]
            reviewer = prompt.split('Your agent name is `')[1].split('`')[0]
            if name == 'q_done':  # 只有这一条复核者真的写下了结论
                recorded.setdefault(name, []).append(dict(agent=reviewer, verdict='faithful'))
            return 0, 'RESULT', 10, False

        with mock.patch.object(s, '_invoke', side_effect=fake_invoke), \
                mock.patch('forge.tasks.load', side_effect=lambda n: states[n]), \
                mock.patch('forge.paper.reviews', side_effect=lambda: recorded):
            summary = s.run_review(root / 'paper.json', root / 'paper.txt')
        reviewed = [p.split('Lean task name: ')[1].split('\n')[0] for p in prompts]
        self.assertEqual(reviewed, ['q_done', 'q_disproved'])
        self.assertIn('kernel verdict in the library: disproved', prompts[1])
        self.assertEqual(summary['outcomes'], {'faithful': 1, 'no_review': 1})

    def _bench_with_outage(self, probe_ok):
        s = self.scheduler.Scheduler('cool', workers=1, max_tasks=20, max_failures=2, cooldowns=1, cooldown_minutes=0)
        items = [dict(name=f'p{i}', statement=': True') for i in range(6)]
        calls = []

        def fake_invoke(prompt, worker, effort=None, seconds=None):
            if worker == 'probe':
                calls.append('probe')
                return (0, 'ok', 1, False) if probe_ok else (1, '', None, False)
            name = prompt.split('Problem name: ')[1].split('\n')[0]
            calls.append(name)
            if name in ('p0', 'p1') and calls.count(name) == 1:  # 前两题第一次碰上 agent 故障（退出码 1、没交文件）
                return 1, '', None, False
            (s.scratch / worker / f'{name}.lean').write_text('x', encoding='utf-8')
            return 0, 'RESULT: solved', 5, False

        with mock.patch.object(s, '_invoke', side_effect=fake_invoke), \
                mock.patch('forge.bench.load', return_value=items), \
                mock.patch('forge.bench.check', return_value=dict(ok=True, kind='proved', solved=True, reason='r')):
            summary = s.run_bench('demo', only_unsolved=False)
        return summary, calls

    def test_agent_outage_triggers_a_cooldown_then_the_run_continues(self):
        summary, calls = self._bench_with_outage(probe_ok=True)
        # 故障中失败的 p0、p1 放回队尾，恢复后补做成功
        self.assertEqual(calls, ['p0', 'p1', 'probe', 'p2', 'p3', 'p4', 'p5', 'p0', 'p1'])
        self.assertEqual(summary['outcomes'], {'unsolved': 2, 'solved': 6})
        self.assertEqual([e['event'] for e in summary['events']], ['cooldown', 'probe'])

    def test_agent_still_down_after_cooldown_stops_the_run(self):
        summary, calls = self._bench_with_outage(probe_ok=False)
        self.assertEqual(calls, ['p0', 'p1', 'probe'])
        self.assertIn('仍不可用', summary['stopped'])

    def test_a_crashing_worker_stops_the_run_visibly(self):
        s = self.scheduler.Scheduler('crash', workers=1, max_tasks=3, max_failures=3)
        with mock.patch('forge.tasks.claim', side_effect=RuntimeError('disk full')):
            summary = s.run_queue()
        self.assertIn('disk full', summary['stopped'])
        self.assertIn('工人', summary['stopped'])

    def test_several_independent_reviews_per_statement(self):
        root = Path(self.tmp.name)
        paper = dict(title='T', arxiv='x', statements=[dict(label='Thm', name='q1', lean=': True', original='o')])
        (root / 'paper.json').write_text(json.dumps(paper), encoding='utf-8')
        (root / 'paper.txt').write_text('text', encoding='utf-8')
        recorded = {'q1': [dict(agent='earlier', verdict='faithful')]}
        s = self.scheduler.Scheduler('rv3', workers=1, max_tasks=10, max_failures=10)
        names = []

        def fake_invoke(prompt, worker):
            reviewer = prompt.split('Your agent name is `')[1].split('`')[0]
            names.append(reviewer)
            recorded['q1'].append(dict(agent=reviewer, verdict='faithful'))
            return 0, 'RESULT', 1, False

        with mock.patch.object(s, '_invoke', side_effect=fake_invoke), \
                mock.patch('forge.tasks.load', return_value=('done', dict(status='proved', closed_by='prover'))), \
                mock.patch('forge.paper.reviews', side_effect=lambda: recorded):
            s.run_review(root / 'paper.json', root / 'paper.txt', reviewers=3)
        self.assertEqual(len(names), 2)  # 已有 1 份独立复核，再补 2 份凑满 3 份
        self.assertEqual(len(set(names)), 2)  # 每份复核都是不同的复核者

    def test_review_consensus_needs_agreement(self):
        from forge import paper
        cases = {('faithful', 'faithful', 'faithful'): 'faithful', ('unfaithful', 'unfaithful', 'faithful'): 'unfaithful',
                 ('faithful', 'unfaithful'): 'disputed', ('faithful', 'unsure', 'faithful'): 'disputed', (): 'unreviewed'}
        for votes, expected in cases.items():
            records = {'t': [dict(agent=f'r{i}', verdict=v) for i, v in enumerate(votes)] + [dict(agent='prover', verdict='faithful')]}
            with mock.patch.object(paper, 'reviews', return_value=records):
                self.assertEqual(paper.review_consensus('t', prover='prover')['verdict'], expected, votes)

    def test_codex_location_can_be_overridden(self):
        with mock.patch.dict(os.environ, {'FORGE_CODEX': r'C:\tools\codex.exe'}):
            self.assertEqual(self.scheduler.find_codex(), r'C:\tools\codex.exe')
        with mock.patch.dict(os.environ, {}, clear=False), mock.patch.dict(os.environ, {'FORGE_CODEX': ''}), \
                mock.patch('shutil.which', return_value=None), mock.patch('pathlib.Path.exists', return_value=False):
            with self.assertRaises(RuntimeError):
                self.scheduler.find_codex()

    def test_scores_from_several_machines_are_merged(self):
        from forge import bench
        root = Path(self.tmp.name)
        with mock.patch.object(bench, 'BENCH', root / 'bench'), mock.patch.object(bench, 'RUNS', root / 'bench' / 'runs'), \
                mock.patch.object(bench, 'load', return_value=[dict(name=f'p{i}') for i in range(4)]):
            (root / 'bench' / 'runs').mkdir(parents=True)
            for machine, rows in (('mac', [('p0', True), ('p2', False)]), ('win', [('p1', True), ('p3', True)])):
                (root / 'bench' / 'runs' / f'demo.r2@{machine}.jsonl').write_text(
                    ''.join(json.dumps(dict(problem=p, solved=s)) + '\n' for p, s in rows), encoding='utf-8')
            combined = bench.score('demo')['combined']
        self.assertEqual(combined, [dict(run='r2', machines=['mac', 'win'], solved=3, total=4, rate=0.75, attempts=4)])


if __name__ == '__main__':
    unittest.main()


class ImproveTests(unittest.TestCase):
    """改进循环的采纳规则：不调用真实 agent。"""

    def setUp(self):
        from forge import improve, scheduler
        self.tmp = tempfile.TemporaryDirectory()
        root = Path(self.tmp.name)
        self.patches = [mock.patch.object(improve, 'STATE', root / 'state.json'),
                        mock.patch.object(improve, 'HISTORY', root / 'history.jsonl'),
                        mock.patch.object(improve, 'PROMPT_DIR', root / 'prompts'),
                        mock.patch.object(scheduler, 'PROMPT_DIR', root / 'prompts')]
        for p in self.patches:
            p.start()
        self.improve, self.root = improve, root

    def tearDown(self):
        for p in self.patches:
            p.stop()
        self.tmp.cleanup()

    def test_better(self):
        better = self.improve.better
        self.assertTrue(better(dict(solved=5, tokens=900), dict(solved=4, tokens=100)))
        self.assertFalse(better(dict(solved=3, tokens=1), dict(solved=4, tokens=100)))
        self.assertTrue(better(dict(solved=4, tokens=80), dict(solved=4, tokens=100)))
        self.assertFalse(better(dict(solved=4, tokens=95), dict(solved=4, tokens=100)))

    def test_check_prompt_rejects_bad_templates(self):
        from forge.scheduler import bench_prompt, check_prompt
        self.assertEqual(check_prompt(bench_prompt('v2')), [])
        self.assertTrue(check_prompt('{name} {statement}'))                       # 缺占位符
        good = bench_prompt('v2')
        self.assertTrue(check_prompt(good + ' {answer}'))                          # 不认识的占位符
        self.assertTrue(check_prompt(good + ' {}'))                                # 位置占位符

    def test_loop_adopts_only_with_holdout_confirmation(self):
        scores = iter([(4, 100), (4, 100),      # 基线：开发集、保留集
                       (5, 120), (3, 90),       # 第 1 轮：开发集更好，保留集变差 → 不采纳
                       (4, 50), (4, 60)])       # 第 2 轮：解出一样多、token 少一半，保留集不变差 → 采纳
        def fake(run, set_name, problems, config, workers, minutes, dry_run=False):
            solved, tokens = next(scores)
            return dict(run=run, solved=solved, problems=len(problems), tokens=tokens, per={})
        with mock.patch.object(self.improve, 'split', return_value=(['a'], ['b'])), \
             mock.patch.object(self.improve, 'evaluate', side_effect=fake), \
             mock.patch.object(self.improve, 'propose_prompt', return_value=('auto001', [])):
            result = self.improve.run_loop('x', iterations=2)
        rows = [json.loads(l) for l in (self.root / 'history.jsonl').read_text().splitlines()]
        self.assertEqual([r.get('decision') for r in rows], [None, 'rejected_on_holdout', 'adopted'])
        self.assertEqual(result['best']['effort'], 'low')
        self.assertEqual(result['best']['prompt'], 'v2')
        self.assertEqual(result['tokens_spent'], 100 + 100 + 120 + 90 + 50 + 60)

    def test_loop_stops_at_token_budget(self):
        def fake(run, set_name, problems, config, workers, minutes, dry_run=False):
            return dict(run=run, solved=1, problems=1, tokens=1000, per={})
        with mock.patch.object(self.improve, 'split', return_value=(['a'], ['b'])), \
             mock.patch.object(self.improve, 'evaluate', side_effect=fake):
            result = self.improve.run_loop('x', iterations=5, token_budget=1500)
        self.assertEqual(result['iterations'], 0)


class AuditTests(unittest.TestCase):
    """批量论文体检：工作项队列与辅助函数，不调用真实 agent。"""

    def test_prefix_and_text(self):
        from forge import audit
        self.assertEqual(audit.prefix_for('2611.07141v1'), 'x2611_07141_')
        text = audit.html_to_text('<html><script>x=1</script><p>Let <math alttext="n\\geq 2"><mi>n</mi></math> be prime.</p>'
                                  '<nav>menu</nav><p>Theorem 1.</p></html>')
        self.assertIn('$n\\geq 2$', text)
        self.assertNotIn('x=1', text)
        self.assertNotIn('menu', text)

    def test_work_queue_runs_every_stage_once(self):
        from forge import audit
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        seen = []
        with mock.patch.object(audit, 'DATA', root), mock.patch('forge.scheduler.RUNS', root / 'runs'), \
             mock.patch('forge.scheduler.DATA', root):
            runner = audit.PaperAudit('t-audit', workers=3, max_tasks=1000, dry_run=True)
            def formalise(agent, paper):
                seen.append(('formalise', paper)); runner._push(('twin', paper, 'a'), ('twin', paper, 'b'))
            def twin(agent, paper, name):
                seen.append(('twin', paper, name)); runner._push(('equiv', paper, name))
            def equiv(agent, paper, name):
                seen.append(('equiv', paper, name))
            runner._formalise, runner._twin, runner._equiv = formalise, twin, equiv
            runner.run_audit(['p1', 'p2'])
        self.assertEqual(len(seen), 2 + 4 + 4)
        self.assertEqual(len(set(seen)), len(seen))


class LockTests(unittest.TestCase):
    def test_lock_is_reentrant_in_one_thread(self):
        from forge import library
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        with mock.patch.object(library, 'DATA', Path(tmp.name)), mock.patch.object(library, 'LOCK', Path(tmp.name) / 'l.lock'):
            done = []
            def nested():
                with library.locked():
                    with library.locked():
                        done.append(1)
            import threading
            t = threading.Thread(target=nested); t.start(); t.join(5)
            self.assertEqual(done, [1], '同一线程嵌套持锁不能死锁')


class ImproveBaselineTests(unittest.TestCase):
    def test_baseline_from_finished_run(self):
        from forge import improve
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        (root / 'runs').mkdir()
        rows = [dict(task='a', outcome='solved', tokens=10, seconds=5), dict(task='b', outcome='unsolved', tokens=20, seconds=6),
                dict(task='c', outcome='solved', tokens=30, seconds=7)]
        (root / 'runs' / 'r0.jsonl').write_text('\n'.join(json.dumps(r) for r in rows))
        with mock.patch('forge.scheduler.RUNS', root / 'runs'):
            score = improve.from_run('r0', ['a', 'b'])
            self.assertEqual((score['solved'], score['tokens']), (1, 30))
            with self.assertRaises(ValueError):
                improve.from_run('r0', ['a', 'zz'])


class ImproveAbortTests(unittest.TestCase):
    def test_incomplete_evaluation_stops_the_loop(self):
        from forge import improve
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        calls = iter([dict(solved=4, tokens=100, complete=True), dict(solved=4, tokens=100, complete=True),
                      dict(solved=0, tokens=0, complete=False, stop_reason='agent 不可用')])
        def fake(run, set_name, problems, config, workers, minutes, dry_run=False):
            return dict(next(calls), run=run, problems=len(problems), per={})
        with mock.patch.object(improve, 'STATE', root / 'state.json'), mock.patch.object(improve, 'HISTORY', root / 'h.jsonl'), \
             mock.patch.object(improve, 'split', return_value=(['a'], ['b'])), \
             mock.patch.object(improve, 'evaluate', side_effect=fake), \
             mock.patch.object(improve, 'propose_prompt', return_value=('p1', [])):
            result = improve.run_loop('x', iterations=5)
        rows = [json.loads(l) for l in (root / 'h.jsonl').read_text().splitlines()]
        self.assertEqual([r['event'] for r in rows], ['baseline', 'aborted'])
        self.assertEqual(result['iterations'], 0)


class PortfolioTests(unittest.TestCase):
    """组合拆解：拼装与作废逻辑，不调用真实 agent。"""

    def test_assemble_body_fills_every_hole(self):
        from forge.portfolio import assemble_body
        body = assemble_body('p', 'theorem p : True ∧ True := by\n  exact ⟨by sorry, by sorry⟩',
                             ['theorem p_d1_h1 : True := trivial'], [('p_d1_h1', [])])
        self.assertNotIn('sorry', body)
        self.assertTrue(body.startswith('theorem p_d1_h1'))
        self.assertIn('exact p_d1_h1', body)

    def test_disproved_lemma_kills_every_dag_using_it(self):
        from forge import portfolio
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        item = dict(name='p', statement=': True')
        with mock.patch.object(portfolio, 'STATE_DIR', root / 'pf'), mock.patch('forge.scheduler.RUNS', root / 'runs'), \
             mock.patch('forge.scheduler.DATA', root), mock.patch.object(portfolio.bench, 'load', return_value=[item]):
            runner = portfolio.Portfolio('t-pf', workers=2, max_tasks=1000, dry_run=True)
            def sketch(agent, problem, k):
                with runner.file_lock:
                    runner.state['lemmas'].setdefault('shared', dict(set='s', problem='p', statement='True', hash='h',
                                                                     status='open', dags=[]))['dags'].append(f'd{k}')
                    runner.state['problems']['p']['dags'][f'd{k}'] = dict(skeleton='', holes=[dict(lemma='shared', args=[])],
                                                                          status='open', planner=agent)
                if k == 1:
                    runner._push(('lemma', 'p', 'shared'))
            def lemma(agent, problem, name):
                with runner.file_lock:
                    runner.state['lemmas'][name]['status'] = 'disproved'
                    for d in runner.state['lemmas'][name]['dags']:
                        runner.state['problems'][problem]['dags'][d]['status'] = 'dead'
            runner._sketch, runner._lemma = sketch, lemma
            result = runner.run_portfolio('s', ['p'], k=3)
        self.assertEqual(result['solved'], 0)
        self.assertEqual({d['status'] for d in runner.state['problems']['p']['dags'].values()}, {'dead'})


class SnapshotPublishTests(unittest.TestCase):
    """forge snapshot 开数据 PR、forge sync 只 fast-forward：用真实 git 仓库和一个假的 gh。"""

    def setUp(self):
        import subprocess
        self.tmp = tempfile.TemporaryDirectory()
        base = Path(self.tmp.name)
        self.origin, self.root, bin_dir = base / 'origin.git', base / 'work', base / 'bin'
        self.log = base / 'gh.log'

        def git(*args, cwd=None):
            return subprocess.run(['git', *args], cwd=cwd or self.root, capture_output=True, text=True, check=True).stdout
        self.git = git
        git('init', '-q', '--bare', '-b', 'main', str(self.origin), cwd=base)
        git('clone', '-q', str(self.origin), str(self.root), cwd=base)
        git('config', 'user.email', 't@example.com'); git('config', 'user.name', 't')
        git('checkout', '-q', '-b', 'main')
        (self.root / 'forge' / 'data').mkdir(parents=True)
        (self.root / 'forge' / 'data' / 'ledger.jsonl').write_text('a\n')
        (self.root / 'app.py').write_text('x = 1\n')
        git('add', '-A'); git('commit', '-q', '-m', 'init'); git('push', '-q', 'origin', 'main')
        bin_dir.mkdir()
        gh = bin_dir / 'gh'
        self.open_prs = base / 'open.json'
        self.open_prs.write_text('[]')
        gh.write_text(f'#!/bin/sh\necho "$@" >> {self.log}\n'
                      f'if [ "$2" = list ]; then cat {self.open_prs}; else echo https://github.com/o/r/pull/7; fi\n')
        gh.chmod(0o755)
        from forge import leanrun, library
        self.patches = [mock.patch.object(leanrun, 'ROOT', self.root), mock.patch.object(library, 'LOCK', base / 'lock'),
                        mock.patch('forge.regressions.consistency', return_value=dict(missing_in_shards=[], missing_in_ledger=[])),
                        mock.patch.dict(os.environ, PATH=f'{bin_dir}{os.pathsep}{os.environ["PATH"]}')]
        for p in self.patches:
            p.start()
        self.library = library

    def tearDown(self):
        for p in reversed(self.patches):
            p.stop()
        self.tmp.cleanup()

    def test_snapshot_pushes_a_data_branch_and_requests_auto_merge(self):
        (self.root / 'forge' / 'data' / 'ledger.jsonl').write_text('a\nb\n')
        (self.root / 'app.py').write_text('x = 2\n')
        result = self.library.snapshot('two entries')
        self.assertTrue(result['ok'] and result['committed'] and result['published'] and result['auto_merge'], result)
        self.assertIn('data/', self.git('ls-remote', '--heads', 'origin'))
        self.assertEqual(self.git('rev-parse', 'origin/main').strip(), self.git('rev-parse', 'HEAD~1').strip())  # main 没被直接推
        self.assertIn('M app.py', self.git('status', '--short'))  # 代码改动没被带进快照
        calls = self.log.read_text()
        self.assertIn('pr create --base main', calls)
        self.assertIn('--auto --squash', calls)

    def test_snapshot_refuses_when_local_main_has_unreviewed_code(self):
        (self.root / 'app.py').write_text('x = 3\n')
        self.git('commit', '-q', '-am', 'code on main')
        result = self.library.snapshot('data')
        self.assertFalse(result['ok'])
        self.assertEqual(result['paths'], ['app.py'])

    def test_include_only_takes_result_paths(self):
        for path in ['app.py', 'forge/data/../../app.py', 'lean/Mathlib2Evil.py']:
            self.assertFalse(self.library.snapshot('x', include=[path])['ok'], path)

    def test_snapshot_reuses_an_open_data_pr(self):
        import json as _json
        (self.root / 'forge' / 'data' / 'ledger.jsonl').write_text('a\nb\n')
        self.git('push', '-q', 'origin', 'main:refs/heads/data/old')
        self.open_prs.write_text(_json.dumps([dict(headRefName='data/old', url='https://github.com/o/r/pull/5')]))
        result = self.library.snapshot('more')
        self.assertTrue(result['ok'] and result['updated_existing_pr'], result)
        self.assertEqual(result['pr'], 'https://github.com/o/r/pull/5')
        self.assertNotIn('pr create', self.log.read_text())
        self.assertEqual(self.git('show', 'data/old:forge/data/ledger.jsonl', cwd=self.origin), 'a\nb\n')
        self.assertEqual(self.git('rev-parse', 'data/old~1', cwd=self.origin).strip(), self.git('rev-parse', 'main', cwd=self.origin).strip())

    def test_snapshot_off_main_commits_locally(self):
        self.git('checkout', '-q', '-b', 'upgrade')
        (self.root / 'forge' / 'data' / 'ledger.jsonl').write_text('a\nb\n')
        result = self.library.snapshot('upgrade data')
        self.assertTrue(result['ok'] and result['committed'] and not result['published'], result)
        self.assertFalse(self.log.exists())

    def test_sync_after_a_squash_merge(self):
        (self.root / 'forge' / 'data' / 'ledger.jsonl').write_text('a\nb\n')
        self.library.snapshot('local', publish=False)
        other = Path(self.tmp.name) / 'squash'
        self.git('clone', '-q', str(self.origin), str(other), cwd=self.tmp.name)
        self.git('config', 'user.email', 't@example.com', cwd=other); self.git('config', 'user.name', 't', cwd=other)
        (other / 'forge' / 'data' / 'ledger.jsonl').write_text('a\nb\n')
        (other / 'app.py').write_text('x = 5\n')
        self.git('commit', '-q', '-am', 'squashed data PR and a code PR', cwd=other); self.git('push', '-q', 'origin', 'main', cwd=other)
        (self.root / 'forge' / 'data' / 'papers.json').write_text('{}')
        result = self.library.sync()
        self.assertTrue(result['ok'], result)
        self.assertEqual(self.git('rev-parse', 'HEAD').strip(), self.git('rev-parse', 'origin/main').strip())
        self.assertEqual((self.root / 'app.py').read_text(), 'x = 5\n')
        self.assertTrue((self.root / 'forge' / 'data' / 'papers.json').exists())

    def test_sync_fast_forwards_and_keeps_uncommitted_data(self):
        other = Path(self.tmp.name) / 'other'
        self.git('clone', '-q', str(self.origin), str(other), cwd=self.tmp.name)
        self.git('config', 'user.email', 't@example.com', cwd=other); self.git('config', 'user.name', 't', cwd=other)
        (other / 'app.py').write_text('x = 9\n')
        self.git('commit', '-q', '-am', 'merged code PR', cwd=other); self.git('push', '-q', 'origin', 'main', cwd=other)
        (self.root / 'forge' / 'data' / 'ledger.jsonl').write_text('a\nunsaved\n')
        result = self.library.sync()
        self.assertTrue(result['ok'], result)
        self.assertEqual((self.root / 'app.py').read_text(), 'x = 9\n')
        self.assertEqual((self.root / 'forge' / 'data' / 'ledger.jsonl').read_text(), 'a\nunsaved\n')

    def test_sync_waits_while_a_data_commit_is_unmerged(self):
        (self.root / 'forge' / 'data' / 'ledger.jsonl').write_text('a\nb\n')
        self.library.snapshot('local only', publish=False)
        self.assertFalse(self.library.sync()['ok'])

    def _squash_merge(self, branch):
        """模拟 GitHub 的 squash 合并：把数据分支的内容作为一个新提交放到 origin 的 main 上。"""
        other = Path(self.tmp.name) / ('gh-' + uuid.uuid4().hex[:6])
        self.git('clone', '-q', str(self.origin), str(other), cwd=self.tmp.name)
        self.git('config', 'user.email', 't@example.com', cwd=other); self.git('config', 'user.name', 't', cwd=other)
        self.git('merge', '-q', '--squash', f'origin/{branch}', cwd=other)
        self.git('commit', '-q', '-m', 'squash', cwd=other); self.git('push', '-q', 'origin', 'main', cwd=other)

    def _data_branch(self):
        return [line.split('refs/heads/')[1] for line in self.git('ls-remote', '--heads', 'origin').splitlines() if 'refs/heads/data/' in line][-1]

    def test_new_data_after_a_squash_merge_publishes_cleanly(self):
        ledger = self.root / 'forge' / 'data' / 'ledger.jsonl'
        ledger.write_text('a\nb\n'); self.library.snapshot('d1')
        ledger.write_text('a\nb\nc\n'); self.library.snapshot('d2', publish=False)
        self._squash_merge(self._data_branch())
        self.assertFalse(self.library.sync()['ok'])  # d2 还没进 origin/main
        self.git('push', '-q', 'origin', '--delete', self._data_branch())
        result = self.library.snapshot('d3')
        self.assertTrue(result['ok'] and result['published'], result)
        self._squash_merge(self._data_branch())  # 新分支建在 origin/main 上，不带旧的 d1，能干净合并
        self.assertTrue(self.library.sync()['ok'])
        self.assertEqual(self.git('show', 'HEAD:forge/data/ledger.jsonl'), 'a\nb\nc\n')

    def test_deleted_include_and_emptied_directory_are_committed(self):
        (self.root / 'reports').mkdir(); (self.root / 'reports' / 'r.txt').write_text('r')
        tasks_dir = self.root / 'forge' / 'data' / 'tasks'; tasks_dir.mkdir(); (tasks_dir / 't.json').write_text('{}')
        self.assertTrue(self.library.snapshot('add', include=['reports/r.txt'], publish=False)['committed'])
        (self.root / 'reports' / 'r.txt').unlink(); (tasks_dir / 't.json').unlink()
        result = self.library.snapshot('remove', include=['reports/r.txt'], publish=False)
        self.assertTrue(result['ok'] and result['committed'], result)
        self.assertEqual(self.git('status', '--short', '--', 'reports', 'forge/data'), '')
        result = self.library.snapshot('nothing', include=['reports/r.txt'], publish=False)  # tasks 目录已空但还在
        self.assertTrue(result['ok'] and not result['committed'], result)
