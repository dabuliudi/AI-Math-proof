"""forge 的测试。纯逻辑部分总是运行；需要真实 Lean 的部分设置 FORGE_INTEGRATION=1 才运行，且不修改库和队列。"""
import contextlib
import hashlib
import json
import os
import tempfile
import threading
import time
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

        def fake_admit_batch(items, tickets=None, _real=library.admit_batch):
            calls.append(len(items))
            return _real(items, tickets)

        # 合并构建失败、回滚后重建、t0 单独构建成功、t1 单独构建失败、回滚后重建
        builds = iter([(1, 'error: duplicate'), (0, ''), (0, ''), (1, 'error'), (0, '')])
        with mock.patch.object(library, 'SHARDS', self.root / 'Shard'), \
                mock.patch.object(library, 'ROOT_FILE', self.root / 'Mathlib2.lean'), \
                mock.patch.object(library, 'LEDGER', self.root / 'ledger.jsonl'), \
                mock.patch.object(library, 'JOURNAL', self.root / 'admit-journal.json'), \
                mock.patch.object(library, 'lake_build', side_effect=lambda target, **_: next(builds)), \
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

    def _library_paths(self):
        from forge import library
        return [mock.patch.object(library, 'SHARDS', self.root / 'Shard'),
                mock.patch.object(library, 'ROOT_FILE', self.root / 'Mathlib2.lean'),
                mock.patch.object(library, 'LEDGER', self.root / 'ledger.jsonl'),
                mock.patch.object(library, 'JOURNAL', self.root / 'admit-journal.json'),
                mock.patch.object(library, 'LOCK', self.root / 'lock'),
                mock.patch.object(library, 'PENDING', self.root / 'pending')]

    def _item(self, name='t0'):
        check = dict(kind='proved', type='True', axioms=[], library_deps=[], external_deps=0, names=[name])
        return dict(name=name, statement=': True'), f'theorem {name} : True := trivial\n', check, 'a'

    def _patched(self, stack, **build):
        from forge import library
        (self.root / 'Mathlib2.lean').write_text('import Mathlib\n', encoding='utf-8')
        for patch in self._library_paths():
            stack.enter_context(patch)
        stack.enter_context(mock.patch.object(library, 'lake_build', **(build or dict(return_value=(0, '')))))

    def _shard_names(self):
        import re
        return [n for p in sorted((self.root / 'Shard').glob('S*.lean'))
                for n in re.findall(r'^-- forge:entry (\S+) ', p.read_text(encoding='utf-8'), re.M)]

    def test_build_timeout_rolls_back(self):
        import subprocess
        from forge import library
        with contextlib.ExitStack() as stack:
            self._patched(stack, side_effect=subprocess.TimeoutExpired('lake', 1))
            result = library.admit_batch([self._item()])
        self.assertFalse(result[0]['ok'])
        self.assertIn('TimeoutExpired', result[0]['reason'])
        self.assertFalse((self.root / 'Shard' / 'S0001.lean').exists())
        self.assertEqual((self.root / 'Mathlib2.lean').read_text(encoding='utf-8'), 'import Mathlib\n')
        self.assertFalse((self.root / 'admit-journal.json').exists())

    def test_ticket_whose_build_raises_does_not_block_later_commits(self):
        # 审查发现：出错的提交回滚后票据留在待入库区，之后每次组提交都带上它、一起失败，库再也进不了东西
        import subprocess
        from forge import library

        def build(target, **_):
            if 'theorem bad ' in ''.join(p.read_text(encoding='utf-8') for p in library.SHARDS.glob('S*.lean')):
                raise subprocess.TimeoutExpired('lake', 1800)
            return 0, ''

        with contextlib.ExitStack() as stack:
            self._patched(stack, side_effect=build)
            outcomes = []
            for name in ('bad', 'good1', 'good2'):
                try:
                    outcomes.append(library.commit(*self._item(name))['ok'])
                except subprocess.TimeoutExpired:
                    outcomes.append('raised')
            ledger = [e['name'] for e in library.entries()]
        self.assertEqual(outcomes, [False, True, True])
        self.assertEqual(ledger, ['good1', 'good2'])
        self.assertEqual(list((self.root / 'pending').glob('*.json')), [])

    def test_stale_journal_does_not_truncate_a_rewritten_ledger(self):
        # 审查发现：回滚日志留下后有别人改了台账（同步、重算哈希），按旧的字节数截断会把台账截在一行中间
        import hashlib
        from forge import library
        with contextlib.ExitStack() as stack:
            self._patched(stack)
            library.admit_batch([self._item('e1')])
            ledger = library.LEDGER.read_bytes()
            library.JOURNAL.write_text(json.dumps(dict(
                names=['e9'], root=library.ROOT_FILE.read_text(encoding='utf-8'), ledger_size=len(ledger),
                ledger_digest=hashlib.sha256(ledger).hexdigest(), shards={}, build=None)), encoding='utf-8')
            entry = library.entries()[0]
            entry['hash'] = 'x' * 40
            library.LEDGER.write_text(json.dumps(entry) + '\n', encoding='utf-8')
            library.admit_batch([self._item('e2')])
            names = [e['name'] for e in library.entries()]
        self.assertEqual(names, ['e1', 'e2'])
        self.assertEqual(self._shard_names(), ['e1', 'e2'])

    def test_stale_journal_does_not_revert_a_shard_changed_since(self):
        from forge import library
        with contextlib.ExitStack() as stack:
            self._patched(stack)
            library.admit_batch([self._item('e1')])
            shard = self.root / 'Shard' / 'S0001.lean'
            ledger = library.LEDGER.read_bytes()
            import hashlib
            library.JOURNAL.write_text(json.dumps(dict(
                names=['e9'], root=library.ROOT_FILE.read_text(encoding='utf-8'), ledger_size=len(ledger),
                ledger_digest=hashlib.sha256(ledger).hexdigest(), shards={str(shard): 'stale text\nend Mathlib2\n'},
                build=None)), encoding='utf-8')
            library.admit_batch([self._item('e2')])
        self.assertEqual(self._shard_names(), ['e1', 'e2'])
        self.assertTrue(list(self.root.glob('admit-journal.rejected-*.json')))

    def test_unreadable_journal_does_not_block_admission(self):
        # 审查发现：空的或写了一半的回滚日志让 json.loads 报错，之后每次入库都失败
        from forge import library
        with contextlib.ExitStack() as stack:
            self._patched(stack)
            library.JOURNAL.write_text('', encoding='utf-8')
            result = library.admit_batch([self._item('x')])
        self.assertTrue(result[0]['ok'])
        self.assertEqual(self._shard_names(), ['x'])

    def test_untrusted_journal_on_inconsistent_library_stops_admission(self):
        from forge import library
        with contextlib.ExitStack() as stack:
            self._patched(stack)
            library.admit_batch([self._item('e1')])
            library.LEDGER.write_text('', encoding='utf-8')  # 分片里有 e1，台账里没有
            library.JOURNAL.write_text('{', encoding='utf-8')
            with self.assertRaises(RuntimeError):
                library.admit_batch([self._item('e2')])
        self.assertEqual(self._shard_names(), ['e1'])

    @unittest.skipIf(os.name == 'nt', 'needs SIGKILL')
    def test_committer_killed_after_ledger_write_does_not_replay_tickets(self):
        # 审查发现：台账写完、票据还没标完成时进程死掉，下一个提交者重放已入库的票据，重复声明构建失败
        import subprocess
        import sys
        script = f"""
import os, signal
from pathlib import Path
from unittest import mock
from forge import library
from forge.tests.test_forge import HardeningTests
case = HardeningTests()
case.root = Path({str(self.root)!r})
for patch in case._library_paths():
    patch.start()
real = Path.write_text
def write_text(self, *args, **kwargs):
    if self.suffix == '.done' or (self.suffix == '.tmp' and '.done.' in self.name):
        os.kill(os.getpid(), signal.SIGKILL)
    return real(self, *args, **kwargs)
real_replace = os.replace
def replace(src, dst):
    if str(dst).endswith('.done'):
        os.kill(os.getpid(), signal.SIGKILL)
    return real_replace(src, dst)
with mock.patch.object(library, 'lake_build', return_value=(0, '')), \\
        mock.patch.object(Path, 'write_text', write_text), mock.patch.object(os, 'replace', replace):
    library.commit(*case._item('A1'))
"""
        (self.root / 'Mathlib2.lean').write_text('import Mathlib\n', encoding='utf-8')
        proc = subprocess.run([sys.executable, '-c', script], cwd=Path(__file__).resolve().parents[2])
        self.assertEqual(proc.returncode, -9)
        from forge import library

        def build(target, **_):
            names = self._shard_names()
            return (1, 'error: already declared') if len(names) != len(set(names)) else (0, '')

        with contextlib.ExitStack() as stack:
            for patch in self._library_paths():
                stack.enter_context(patch)
            stack.enter_context(mock.patch.object(library, 'lake_build', side_effect=build))
            result = library.commit(*self._item('C1'))
            ledger = [e['name'] for e in library.entries()]
        self.assertTrue(result['ok'])
        self.assertEqual(ledger, ['A1', 'C1'])
        self.assertEqual(self._shard_names(), ['A1', 'C1'])
        self.assertEqual(list((self.root / 'pending').glob('*.json')), [])
        for done in (self.root / 'pending').glob('*.done'):
            self.assertTrue(json.loads(done.read_text(encoding='utf-8'))['ok'])

    @unittest.skipIf(os.name == 'nt', 'needs process groups')
    def test_lake_build_timeout_kills_the_whole_build(self):
        # 审查发现：subprocess.run 超时只杀 lake，它起的 lean 留下来跟下一次构建抢资源
        import subprocess
        from forge import leanrun
        pidfile = self.root / 'child.pid'
        fake = self.root / 'lake'
        fake.write_text(f'#!/bin/sh\nsleep 30 &\necho $! > {pidfile}\nwait\n', encoding='utf-8')
        fake.chmod(0o755)
        with mock.patch.object(leanrun, 'find_lake', return_value=str(fake)):
            with self.assertRaises(subprocess.TimeoutExpired):
                # 超时要留够让假 lake 起来并写下子进程号：整套测试一起跑时 shell 启动可能超过 1 秒
                leanrun.lake_build('Mathlib2', timeout=5)
        child = int(pidfile.read_text())
        deadline = time.time() + 5
        alive = True
        while alive and time.time() < deadline:
            try:
                os.kill(child, 0)
                time.sleep(0.1)
            except ProcessLookupError:
                alive = False
        if alive:
            os.kill(child, 9)
        self.assertFalse(alive, 'the build left a child process running')

    @unittest.skipIf(os.name == 'nt', 'needs SIGKILL')
    def test_admission_killed_mid_build_is_undone_by_next_admission(self):
        # 事故：提交进程在构建中途被结束，分片留着没进台账的条目，下一次入库又把同一条追加了一遍
        import signal
        import subprocess
        import sys
        from forge import library
        (self.root / 'Mathlib2.lean').write_text('import Mathlib\n', encoding='utf-8')
        script = f"""
import time
from pathlib import Path
from unittest import mock
from forge import library
from forge.tests.test_forge import HardeningTests
root = Path({str(self.root)!r})
def hang(target, **_):
    (root / 'build-started').write_text('')
    time.sleep(60)
case = HardeningTests()
case.root = root
for patch in case._library_paths():
    patch.start()
with mock.patch.object(library, 'lake_build', side_effect=hang):
    library.admit_batch([case._item()])
"""
        proc = subprocess.Popen([sys.executable, '-c', script], cwd=Path(__file__).resolve().parents[2])
        try:
            deadline = time.time() + 60
            while not (self.root / 'build-started').exists():
                self.assertIsNone(proc.poll(), 'admission subprocess exited early')
                self.assertLess(time.time(), deadline)
                time.sleep(0.05)
        finally:
            proc.send_signal(signal.SIGKILL)
            proc.wait()
        with contextlib.ExitStack() as stack:
            for patch in self._library_paths():
                stack.enter_context(patch)
            stack.enter_context(mock.patch.object(library, 'lake_build', return_value=(0, '')))
            result = library.admit_batch([self._item()])
        self.assertTrue(result[0]['ok'])
        shard = (self.root / 'Shard' / 'S0001.lean').read_text(encoding='utf-8')
        self.assertEqual(shard.count('-- forge:entry t0 '), 1)
        self.assertEqual(len((self.root / 'ledger.jsonl').read_text(encoding='utf-8').splitlines()), 1)
        self.assertFalse((self.root / 'admit-journal.json').exists())

    def test_concurrent_commits_share_one_build(self):
        from forge import library
        builds = []
        gate = threading.Event()

        def slow_build(target, **_):
            builds.append(target)
            gate.wait(2)  # 第一次构建期间其余提交排进待入库区
            return 0, ''

        with mock.patch.object(library, 'SHARDS', self.root / 'Shard'), \
                mock.patch.object(library, 'ROOT_FILE', self.root / 'Mathlib2.lean'), \
                mock.patch.object(library, 'LEDGER', self.root / 'ledger.jsonl'), \
                mock.patch.object(library, 'JOURNAL', self.root / 'admit-journal.json'), \
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


class BenchStaticRejectionTests(unittest.TestCase):
    def test_malformed_submission_is_an_unsolved_attempt(self):
        from forge import bench
        body = 'theorem p : True := trivial\ntheorem p_aux1 : True := trivial\n'   # 主定理不在最后
        with tempfile.TemporaryDirectory() as tmp, \
                mock.patch.object(bench, 'load', return_value=[dict(name='p', statement=': True')]), \
                mock.patch.object(bench, 'RUNS', Path(tmp)):
            verdict = bench.check('demo', 'p', body, 'r', 'a')
            self.assertFalse(verdict['solved'])
            self.assertIn('最后一个声明必须是主定理', verdict['reason'])
            record = json.loads((Path(tmp) / 'demo.r.jsonl').read_text(encoding='utf-8'))
            self.assertFalse(record['solved'])

    def test_check_submission_returns_a_verdict_for_malformed_files(self):
        from forge.verify import check_submission
        task = dict(name='p', statement=': True')
        only_helper = check_submission(task, 'theorem p_aux1 : True := trivial\n')
        self.assertFalse(only_helper['ok'])
        self.assertIn('提交格式不合规', only_helper['reason'])
        disproof = check_submission(task, 'theorem p_disproof : ¬ True := sorry\ntheorem p_aux1 : True := trivial\n')
        self.assertEqual(disproof['kind'], 'disproved')

    def test_malformed_bench_statement_still_raises(self):
        from forge.statement import StatementError
        from forge.verify import check_submission
        with mock.patch('forge.verify.run_source') as lean:
            with self.assertRaises(StatementError):
                check_submission(dict(name='p', statement='True := trivial'), 'theorem p : True := trivial\n')
            lean.assert_not_called()


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
        self.patches = [mock.patch.object(scheduler, 'RUNS', root / 'runs'), mock.patch.object(scheduler, 'DATA', root),
                        mock.patch.object(scheduler, 'SCRATCH', root / 'scratch'),
                        mock.patch('forge.provenance.SCRATCH', root / 'scratch'), mock.patch('forge.provenance.LEGACY', ()),
                        mock.patch('forge.provenance.checkouts', lambda: [Path('/nonexistent-checkout')])]
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

        def fake_check(set_name, problem, body, run, agent, before=None):
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

        def fake_check(set_name, problem, body, run, agent, before=None):
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


class CopyIsolationTests(unittest.TestCase):
    """事故（2026-11-17）：评测 agent 读得到以前各轮留下的证明，改进循环里有题是抄来的。"""

    PROOF = '\n'.join(f'  have h{i} : some_long_fact_number_{i} = other_side_{i} := by ring_nf' for i in range(8))

    def setUp(self):
        from forge import scheduler
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.patches = [mock.patch.object(scheduler, 'RUNS', self.root / 'runs'), mock.patch.object(scheduler, 'DATA', self.root),
                        mock.patch.object(scheduler, 'SCRATCH', self.root / 'scratch'),
                        mock.patch('forge.provenance.SCRATCH', self.root / 'scratch'), mock.patch('forge.provenance.LEGACY', ()),
                        mock.patch('forge.provenance.checkouts', lambda: [Path('/nonexistent-checkout')])]
        for p in self.patches:
            p.start()
        self.scheduler = scheduler

    def tearDown(self):
        for p in self.patches:
            p.stop()
        self.tmp.cleanup()

    def _old_file(self, rel, text, age=3600):
        path = self.root / 'scratch' / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding='utf-8')
        old = time.time() - age
        os.utime(path, (old, old))
        return path

    def test_check_flags_only_files_older_than_the_run(self):
        from forge import provenance
        source = self._old_file('agents/old-run/w0/p.lean', 'theorem p : True := by\n' + self.PROOF)
        verdict = provenance.check('theorem p : True := by\n' + self.PROOF, time.time())
        self.assertTrue(verdict['copied'])
        self.assertEqual(verdict['source'], str(source))
        self.assertFalse(provenance.check(self.PROOF, time.time() - 7200)['copied'])   # 文件比本轮新：不算来源

    def test_short_or_common_lines_are_not_a_copy(self):
        from forge import provenance
        self._old_file('agents/old/w0/p.lean', 'theorem p : True := by\n  simp\n  omega\n' + self.PROOF.splitlines()[0])
        verdict = provenance.check('theorem p : True := by\n  simp\n  omega\n' + self.PROOF.splitlines()[0], time.time())
        self.assertFalse(verdict['copied'])   # 只有 1 行够长且相同，少于 MIN_SHARED

    def test_portfolio_state_json_is_a_source(self):
        from forge import provenance
        self._old_file('portfolio/pf.json', json.dumps(dict(lemmas=dict(L=dict(proof=self.PROOF)))))
        self.assertTrue(provenance.check(self.PROOF, time.time())['copied'])

    def test_scratch_lives_outside_the_repo_and_is_writable_for_the_agent(self):
        s = self.scheduler.Scheduler('iso', workers=1)
        self.assertEqual(s.scratch, self.root / 'scratch' / 'agents' / 'iso')
        with mock.patch.object(self.scheduler, 'find_codex', return_value='codex'):
            cmd = s._command(s.scratch / 'w.last.txt')
        self.assertEqual(cmd[cmd.index('--add-dir') + 1], str(s.scratch))
        from forge.leanrun import ROOT, SCRATCH
        self.assertNotIn(ROOT, SCRATCH.parents)

    def test_lean_check_files_are_written_outside_the_repo_and_removed(self):
        from forge import leanrun
        seen = []
        class FakeProc:
            pid, returncode = 1, 0
            def __init__(self, command, **kw):
                seen.append(Path(command[-1]))
            def communicate(self, timeout=None):
                return '', ''
        checks = self.root / 'scratch' / 'checks'
        lake = mock.patch.object(leanrun, 'find_lake', return_value='lake')   # CI 上没装 Lean
        lake.start(); self.addCleanup(lake.stop)
        with mock.patch.object(leanrun, 'CHECKS', checks), mock.patch.object(leanrun.subprocess, 'Popen', FakeProc):
            leanrun.run_source('theorem t : True := trivial\n')
        self.assertEqual(seen[0].parent, checks)
        self.assertTrue(seen[0].name.startswith(f'check_{os.getpid()}_'))
        self.assertNotIn(leanrun.ROOT, leanrun.CHECKS.parents)
        self.assertFalse(seen[0].exists())
        with mock.patch.object(leanrun, 'CHECKS', checks), \
                mock.patch.object(leanrun.subprocess, 'Popen', side_effect=FileNotFoundError('lake')):
            with self.assertRaises(FileNotFoundError):
                leanrun.run_source('theorem t : True := trivial\n')
        self.assertEqual(list(checks.iterdir()), [])   # 出错也删

    def test_sweep_removes_check_files_of_dead_processes_only(self):
        from forge import leanrun
        checks = self.root / 'scratch' / 'checks'
        checks.mkdir(parents=True)
        live = checks / f'check_{os.getpid()}_aa.lean'
        dead = checks / 'check_999999999_bb.lean'
        old = checks / 'check_0123456789abcdef.lean'   # 旧文件名，认不出进程号
        new = checks / 'check_fedcba9876543210.lean'
        odd = [checks / 'check_4294967296_x.lean', checks / 'check_²_x.lean']   # 进程号溢出、非 ASCII 数字
        for path in (live, dead, old, new, *odd):
            path.write_text('x', encoding='utf-8')
        os.utime(old, (time.time() - 2 * leanrun.CHECK_MAX_AGE,) * 2)
        with mock.patch.object(leanrun, 'CHECKS', checks), mock.patch.object(leanrun, '_swept', [0.0]):
            leanrun._sweep_checks()
        self.assertEqual(sorted(p.name for p in checks.iterdir()), sorted([live.name, new.name] + [p.name for p in odd]))

    def test_lean_check_files_are_not_copy_sources(self):
        from forge import provenance
        self._old_file('checks/check_1_ab.lean', self.PROOF)
        with mock.patch.object(provenance, 'CHECKS', self.root / 'scratch' / 'checks'):
            self.assertFalse(provenance.check(self.PROOF, time.time())['copied'])

    def test_other_worktrees_old_drafts_are_sources(self):
        from forge import provenance
        other = self.root / 'other-checkout'
        draft = other / 'forge' / 'data' / 'staging' / 'portfolio' / 'pf.json'
        draft.parent.mkdir(parents=True)
        draft.write_text(json.dumps(dict(lemmas=dict(L=dict(proof=self.PROOF)))), encoding='utf-8')
        os.utime(draft, (time.time() - 3600,) * 2)
        with mock.patch.object(provenance, 'checkouts', lambda: [provenance.ROOT, other]):
            self.assertEqual(provenance.check(self.PROOF, time.time())['source'], str(draft))
            self.assertFalse(provenance.check(self.PROOF, time.time(), exclude=[draft])['copied'])
        self.assertFalse(provenance.check(self.PROOF, time.time())['copied'])   # 只有当前检出时看不到

    def test_checkouts_lists_every_worktree_once(self):
        from forge import provenance
        real = next(p for p in self.patches if p.attribute == 'checkouts').temp_original   # setUp 换掉了它
        out = (f'worktree {provenance.ROOT}\nHEAD abc\nbranch refs/heads/main\n\n'
               'worktree /x/wt-a\nHEAD def\nbranch refs/heads/a\n\nworktree /x/wt-b\nHEAD 123\ndetached\n')
        with mock.patch.object(provenance, '_checkouts', [0.0, None]):
            with mock.patch.object(provenance.subprocess, 'run', return_value=mock.Mock(stdout=out)) as run:
                self.assertEqual(real(), [provenance.ROOT, Path('/x/wt-a'), Path('/x/wt-b')])
                real()
            self.assertEqual(run.call_count, 1)   # 缓存
        cache = [0.0, None]
        with mock.patch.object(provenance, '_checkouts', cache), \
                mock.patch.object(provenance.subprocess, 'run', side_effect=OSError):
            self.assertEqual(real(), [provenance.ROOT])
        self.assertIsNone(cache[1])   # 失败不缓存

    def _bench(self, run, agent_writes):
        s = self.scheduler.Scheduler(run, workers=1, max_tasks=5, max_failures=5)
        def fake_invoke(prompt, worker):
            if agent_writes is not None:
                (s.scratch / worker / 'p.lean').write_text(agent_writes, encoding='utf-8')
            return 0, 'RESULT: solved', 10, False
        checked = []
        def fake_check(set_name, problem, body, run, agent, before=None):
            from forge import provenance   # 只替掉 Lean 检查，抄写检测照常做
            checked.append(body)
            return dict(ok=True, kind='proved', solved=True, reason='通过', copy=provenance.check(body, before))
        with mock.patch.object(s, '_invoke', side_effect=fake_invoke), \
                mock.patch('forge.bench.load', return_value=[dict(name='p', statement=': True')]), \
                mock.patch('forge.bench.check', side_effect=fake_check):
            s.run_bench('demo', only_unsolved=False)
        return s, checked

    def test_bench_record_marks_a_copied_solve(self):
        self._old_file('agents/pf-old/w3/p.d1.final.lean', 'theorem p : True := by\n' + self.PROOF)
        s, _ = self._bench('cp', 'theorem p : True := by\n' + self.PROOF)
        row = s.records[0]
        self.assertEqual(row['outcome'], 'solved')
        self.assertTrue(row['copied'])
        self.assertIn('pf-old', row['copy_source'])

    def test_bench_record_of_an_original_solve(self):
        self._old_file('agents/pf-old/w3/q.lean', 'theorem q : True := by\n' + self.PROOF)
        s, _ = self._bench('orig', 'theorem p : True := by\n' + self.PROOF.replace('ring_nf', 'nlinarith [sq_nonneg x]'))
        self.assertFalse(s.records[0]['copied'])

    def test_a_proof_left_by_an_earlier_run_of_the_same_name_is_not_a_solve(self):
        stale = self._old_file('agents/same/same-w0/p.lean', 'theorem p : True := trivial')
        s, checked = self._bench('same', None)   # agent 什么都没写
        self.assertEqual(checked, [])
        self.assertEqual(s.records[0]['outcome'], 'unsolved')
        self.assertFalse(stale.exists())
        self.assertEqual(len(list(stale.parent.glob('p.stale-*.lean'))), 1)

    def test_old_attempt_drafts_are_moved_aside_too(self):
        draft = self._old_file('agents/lad2/lad2-w0/p.attempt1.lean', 'old draft')
        self._bench('lad2', None)
        self.assertFalse(draft.exists())
        self.assertEqual(len(list(draft.parent.glob('p.attempt1.stale-*.lean'))), 1)

    def test_excluded_folders_are_not_sources(self):
        from forge import provenance
        own = self._old_file('agents/pf-run/w0/L.proved.lean', self.PROOF)
        self.assertTrue(provenance.check(self.PROOF, time.time())['copied'])
        self.assertFalse(provenance.check(self.PROOF, time.time(), exclude=[own.parent.parent])['copied'])

    def test_compare_and_only_unsolved_ignore_copied_solves(self):
        runs = self.root / 'runs'
        runs.mkdir(parents=True, exist_ok=True)
        rows = [dict(task='a', outcome='solved', copied=True, seconds=1), dict(task='b', outcome='solved', copied=False, seconds=1)]
        (runs / 'cmp.jsonl').write_text('\n'.join(json.dumps(r) for r in rows))
        row = self.scheduler.compare(['cmp'])['runs'][0]
        self.assertEqual(row['solved'], 1)
        from forge import bench
        (runs / 'demo.r.jsonl').write_text('\n'.join(json.dumps(dict(problem=p, solved=True, copied=c, agent='scheduler'))
                                                     for p, c in (('a', True), ('b', False))))
        s = self.scheduler.Scheduler('ou', workers=1)
        with mock.patch.object(bench, 'RUNS', runs), mock.patch('forge.bench.load', return_value=[dict(name='a'), dict(name='b')]), \
                mock.patch.object(s, '_run_threads', side_effect=lambda fn, args: [i['name'] for i in args[1]]):
            self.assertEqual(s.run_bench('demo', only_unsolved=True), ['a'])

    def test_bench_score_leaves_out_copied_solves(self):
        from forge import bench
        runs = self.root / 'runs'
        runs.mkdir(parents=True, exist_ok=True)
        rows = [dict(problem='a', solved=True, copied=True), dict(problem='b', solved=True, copied=False), dict(problem='c', solved=True)]
        (runs / 'demo.r1.jsonl').write_text('\n'.join(json.dumps(r) for r in rows))
        with mock.patch.object(bench, 'RUNS', runs), mock.patch.object(bench, 'load', return_value=[dict(name=n) for n in 'abcd']):
            row = next(r for r in bench.score('demo')['runs'] if r['run'] == 'r1')
        self.assertEqual(row['solved'], 2)

    def test_bench_check_records_the_copy(self):
        from forge import bench
        self._old_file('agents/pf-old/w3/p.final.lean', 'theorem p : True := by\n' + self.PROOF)
        runs = self.root / 'runs'
        with mock.patch.object(bench, 'RUNS', runs), mock.patch.object(bench, 'load', return_value=[dict(name='p', statement=': True')]), \
                mock.patch.object(bench, 'check_submission', return_value=dict(ok=True, kind='proved', reason='通过')):
            verdict = bench.check('demo', 'p', 'theorem p : True := by\n' + self.PROOF, 'r2', 'scheduler', before=time.time())
            self.assertTrue(verdict['copy']['copied'])
            self.assertFalse(bench.check('demo', 'p', 'theorem p : True := by\n' + self.PROOF, 'r2', 'x')['copy'])  # 没给 before：不检测
        row = json.loads((runs / 'demo.r2.jsonl').read_text().splitlines()[0])
        self.assertTrue(row['copied'])


class ImproveCopyTests(unittest.TestCase):
    def test_copied_solves_do_not_count(self):
        from forge import improve
        per = improve._tally([dict(task='a', outcome='solved', copied=True, copy_source='x.lean', tokens=1, seconds=1),
                              dict(task='b', outcome='solved', copied=False, tokens=1, seconds=1),
                              dict(task='c', outcome='solved', tokens=1, seconds=1),          # 旧记录没有检测字段
                              dict(task='d', outcome='unsolved', tokens=1, seconds=1)])
        score = improve._score('r', ['a', 'b', 'c', 'd'], per)
        self.assertEqual(score['solved'], 2)
        self.assertEqual(score['copied'], ['a'])

    def test_old_state_is_rechecked_before_any_candidate(self):
        from forge import improve
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        best = dict(config=dict(prompt='auto003', effort='xhigh'), dev=dict(solved=11, tokens=100, per={}),
                    holdout=dict(solved=12, tokens=100, per={}))
        (root / 'state-x.json').write_text(json.dumps(dict(best=best, iteration=4, tokens_spent=0, set='x', dev=['a'], holdout=['b'])))
        runs = []
        def fake(run, set_name, problems, config, workers, minutes, dry_run=False):
            runs.append((run, config['prompt']))
            return dict(run=run, solved=9, problems=1, tokens=10, per={}, copied=['a'], complete=True)
        with mock.patch.object(improve, 'STATE', root / 'state.json'), mock.patch.object(improve, 'HISTORY', root / 'h.jsonl'), \
             mock.patch.object(improve, 'split', return_value=(['a'], ['b'])), \
             mock.patch.object(improve, 'evaluate', side_effect=fake):
            improve.run_loop('x', iterations=0)
        self.assertEqual(runs, [('improve-x-004-recheck-dev', 'auto003'), ('improve-x-004-recheck-holdout', 'auto003')])
        state = json.loads((root / 'state-x.json').read_text())
        self.assertTrue(state['copy_checked'])
        self.assertEqual((state['best']['dev']['solved'], state['best']['holdout']['solved']), (9, 9))
        row = json.loads((root / 'h.jsonl').read_text().splitlines()[-1])
        self.assertEqual((row['event'], row['old_dev_solved'], row['dev_copied']), ('recheck', 11, ['a']))

    def _old_state(self, root, tokens_spent=0):
        best = dict(config=dict(prompt='auto003', effort='xhigh'), dev=dict(solved=11, tokens=100, per={}),
                    holdout=dict(solved=12, tokens=100, per={}))
        (root / 'state-x.json').write_text(json.dumps(dict(best=best, iteration=4, tokens_spent=tokens_spent, set='x',
                                                            dev=['a'], holdout=['b'])))

    def _run(self, root, **kw):
        from forge import improve
        runs = []
        def fake(run, set_name, problems, config, workers, minutes, dry_run=False):
            runs.append(run)
            return dict(run=run, solved=0, problems=1, tokens=0, per={}, copied=[], complete=True)
        with mock.patch.object(improve, 'STATE', root / 'state.json'), mock.patch.object(improve, 'HISTORY', root / 'h.jsonl'), \
             mock.patch.object(improve, 'split', return_value=(['a'], ['b'])), \
             mock.patch.object(improve, 'evaluate', side_effect=fake):
            improve.run_loop('x', iterations=0, **kw)
        return runs, json.loads((root / 'state-x.json').read_text())

    def test_baseline_run_without_copy_fields_is_rechecked(self):
        from forge import improve
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        (root / 'runs').mkdir()
        rows = [dict(task='a', outcome='solved', tokens=1, seconds=1), dict(task='b', outcome='solved', tokens=1, seconds=1)]
        (root / 'runs' / 'old.jsonl').write_text('\n'.join(json.dumps(r) for r in rows))
        runs = []
        def fake(run, set_name, problems, config, workers, minutes, dry_run=False):
            runs.append(run)
            return dict(run=run, solved=1, problems=1, tokens=0, per={}, copied=[], complete=True)
        with mock.patch('forge.scheduler.RUNS', root / 'runs'), mock.patch.object(improve, 'STATE', root / 'state.json'), \
             mock.patch.object(improve, 'HISTORY', root / 'h.jsonl'), mock.patch.object(improve, 'split', return_value=(['a'], ['b'])), \
             mock.patch.object(improve, 'evaluate', side_effect=fake):
            improve.run_loop('x', iterations=0, baseline_run='old')
        self.assertEqual(runs, ['improve-x-000-recheck-dev', 'improve-x-000-recheck-holdout'])

    def test_dry_run_does_not_overwrite_the_best_with_empty_scores(self):
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        self._old_state(root)
        runs, state = self._run(root, dry_run=True)
        self.assertEqual(runs, [])
        self.assertEqual(state['best']['dev']['solved'], 11)
        self.assertNotIn('copy_checked', state)

    def test_recheck_respects_the_token_budget(self):
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        self._old_state(root, tokens_spent=10_000)
        runs, state = self._run(root, token_budget=5_000)
        self.assertEqual(runs, [])
        self.assertNotIn('copy_checked', state)


class PortfolioLegacyStateTests(unittest.TestCase):
    def test_runs_started_before_the_move_resume_from_the_old_place(self):
        from forge import portfolio
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        (root / 'old').mkdir()
        (root / 'old' / 'pf-k6-1.json').write_text('{}')
        with mock.patch.object(portfolio, 'STATE_DIR', root / 'new'), mock.patch.object(portfolio, 'LEGACY_STATE_DIR', root / 'old'):
            self.assertEqual(portfolio._state_path('pf-k6-1'), root / 'old' / 'pf-k6-1.json')
            self.assertEqual(portfolio._state_path('pf-new'), root / 'new' / 'pf-new.json')


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
        # 评测检查器要求附加定理叫 `<题名>_aux…`：引理和用到它的地方一起改名
        self.assertTrue(body.startswith('theorem p_aux_d1_h1'))
        self.assertIn('exact p_aux_d1_h1', body)
        self.assertNotIn('p_d1_h1', body)

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

    def test_aux_names_renames_only_whole_lemma_names(self):
        from forge.portfolio import aux_names
        self.assertEqual(aux_names('p', 'theorem p_d1_h1 pp_d1_h1 Foo.p_d1_h1 (p_d12_h3)'),
                         'theorem p_aux_d1_h1 pp_d1_h1 Foo.p_d1_h1 (p_aux_d12_h3)')

    def _runner(self, root, item):
        from forge import portfolio
        stack = contextlib.ExitStack(); self.addCleanup(stack.close)
        for patch in (mock.patch.object(portfolio, 'STATE_DIR', root / 'pf'), mock.patch('forge.scheduler.RUNS', root / 'runs'),
                      mock.patch('forge.scheduler.DATA', root), mock.patch.object(portfolio.bench, 'load', return_value=[item])):
            stack.enter_context(patch)
        return portfolio, portfolio.Portfolio('t-pf', workers=1, max_tasks=1000, dry_run=True)

    def test_malformed_lemma_submission_is_unsolved_not_a_dead_dag(self):
        from forge.statement import StatementError
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        portfolio, runner = self._runner(root, dict(name='p', statement=': True'))
        runner.items = {'p': dict(name='p', statement=': True')}
        runner.state = dict(run='t-pf', problems={'p': dict(set='s', solved_by=None, dags={'d1': dict(skeleton='', holes=[dict(lemma='L', args=[])], status='open')})},
                            lemmas={'L': dict(set='s', problem='p', statement='True', hash='h', status='open', dags=['d1'])})
        runner.file_lock, runner.lemma_seconds, runner.scratch, runner.lemma_attempts = threading.Lock(), 60, root / 'scratch', 1

        def invoke(prompt, agent, seconds=None):
            (root / 'scratch' / agent).mkdir(parents=True, exist_ok=True)
            (root / 'scratch' / agent / 'L.lean').write_text('theorem L : True := by sorry')
            return 0, '', 0, False
        with mock.patch.object(runner, '_invoke', side_effect=invoke), \
                mock.patch('forge.verify.check_submission', side_effect=StatementError('剩下 sorry')):
            runner._lemma('a1', 'p', 'L')
        self.assertEqual(runner.state['lemmas']['L']['status'], 'unsolved')
        self.assertEqual(runner.state['problems']['p']['dags']['d1']['status'], 'open')

    def test_failing_lemma_check_does_not_take_the_library_lock(self):
        # 子引理检查不导入 Mathlib2，库重建与它无关：没过的检查不该再持全局入库锁重跑一遍
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        portfolio, runner = self._runner(root, dict(name='p', statement=': True'))
        runner.items = {'p': dict(name='p', statement=': True')}
        runner.state = dict(run='t-pf', problems={'p': dict(set='s', solved_by=None, dags={'d1': dict(skeleton='', holes=[dict(lemma='L', args=[])], status='open')})},
                            lemmas={'L': dict(set='s', problem='p', statement='True', hash='h', status='open', dags=['d1'])})
        runner.file_lock, runner.lemma_seconds, runner.scratch, runner.lemma_attempts = threading.Lock(), 60, root / 'scratch', 1

        def invoke(prompt, agent, seconds=None):
            (root / 'scratch' / agent).mkdir(parents=True, exist_ok=True)
            (root / 'scratch' / agent / 'L.lean').write_text('theorem L : True := by simp')
            return 0, '', 0, False
        failing = dict(ok=False, reason='Lean 报错', errors=['type mismatch'])
        with mock.patch.object(runner, '_invoke', side_effect=invoke), \
                mock.patch('forge.verify.check_submission', return_value=failing) as check, \
                mock.patch('forge.library.locked', side_effect=AssertionError('took the library lock')):
            runner._lemma('a1', 'p', 'L')
        self.assertEqual(check.call_count, 1)
        self.assertEqual(runner.state['lemmas']['L']['status'], 'unsolved')

    def test_resume_clears_stale_queued_flags(self):
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        portfolio, runner = self._runner(root, dict(name='p', statement=': True'))
        (root / 'pf').mkdir()
        (root / 'pf' / 't-pf.json').write_text(json.dumps(dict(run='t-pf', problems={'p': dict(set='s', solved_by=None, dags={
            'd1': dict(skeleton='', holes=[dict(lemma='L', args=[])], status='dead')})}, lemmas={
            'L': dict(set='s', problem='p', statement='True', hash='h', status='open', dags=['d1'], queued=True)})))
        seen = []
        runner._sketch = lambda agent, problem, k: seen.append(runner.state['lemmas']['L'].get('queued'))
        runner.run_portfolio('s', ['p'], k=2)
        self.assertEqual(seen, [False])  # 重新拆解时这条引理不再被旧的排队标记挡住

    def test_library_task_closed_field_cannot_change_what_is_proved(self):
        from forge import verify
        seen = []

        def capture(source, **kwargs):
            seen.append(source)
            raise RuntimeError('stop')
        task = dict(name='t', statement=': 1 + 1 = 3', closed='True', opens='', preamble='', imports=[])
        with mock.patch.object(verify, 'run_source', side_effect=capture):
            with self.assertRaises(RuntimeError):
                verify.check_submission(task, 'theorem t : True := trivial')
        self.assertIn('(1 + 1 = 3)', seen[0])
        self.assertNotIn('"proved" (True)', seen[0])


class SnapshotPublishTests(unittest.TestCase):
    """forge snapshot 开或更新本检出自己的数据 PR、forge sync 对齐 origin/main：用真实 git 仓库和一个记着 PR 状态的假 gh。"""

    GH = r"""#!/usr/bin/env python3
import json, sys
from pathlib import Path
store, log = Path(sys.argv[0]).with_name('prs.json'), Path(sys.argv[0]).with_name('gh.log')
with open(log, 'a') as f:
    f.write(' '.join(sys.argv[1:]) + '\n')
prs = json.loads(store.read_text()) if store.exists() else {}
args = sys.argv[1:]
if args[:2] == ['pr', 'create']:
    head = args[args.index('--head') + 1]
    prs[head] = dict(state='OPEN', url=f'https://github.com/o/r/pull/{100 + len(prs)}', isCrossRepository=False, autoMergeRequest=None)
    print(prs[head]['url'])
elif args[:2] == ['pr', 'view']:
    pr = prs.get(args[2])
    if not pr:
        sys.exit(1)
    flip = pr.pop('flip_after', None)
    if flip is not None:
        if flip == 0:
            pr['state'] = 'MERGED'
        else:
            pr['flip_after'] = flip - 1
    print(json.dumps({k: v for k, v in pr.items() if k != 'flip_after'}))
elif args[:2] == ['pr', 'merge']:
    for pr in prs.values():
        if pr['url'] == args[2]:
            pr['autoMergeRequest'] = dict(mergeMethod='SQUASH')
store.write_text(json.dumps(prs))
"""

    def setUp(self):
        import subprocess
        self.tmp = tempfile.TemporaryDirectory()
        self.base = Path(self.tmp.name)
        self.origin, bin_dir = self.base / 'origin.git', self.base / 'bin'

        def git(*args, cwd=None):
            return subprocess.run(['git', *args], cwd=cwd or self.root, capture_output=True, text=True, check=True).stdout
        self.git = git
        git('init', '-q', '--bare', '-b', 'main', str(self.origin), cwd=self.base)
        self.root = self._clone('work')
        (self.root / 'forge' / 'data').mkdir(parents=True)
        self._write('forge/data/ledger.jsonl', 'a\n')
        self._write('app.py', 'x = 1\n')
        git('add', '-A'); git('commit', '-q', '-m', 'init'); git('push', '-q', 'origin', 'main')
        bin_dir.mkdir()
        gh = bin_dir / 'gh'
        gh.write_text(self.GH); gh.chmod(0o755)
        self.prs, self.log = bin_dir / 'prs.json', bin_dir / 'gh.log'
        from forge import leanrun, library
        self.root_patch = mock.patch.object(leanrun, 'ROOT', self.root)
        self.patches = [self.root_patch, mock.patch.object(library, 'LOCK', self.base / 'lock'),
                        mock.patch('forge.regressions.consistency', return_value=dict(missing_in_shards=[], missing_in_ledger=[])),
                        mock.patch.dict(os.environ, PATH=f'{bin_dir}{os.pathsep}{os.environ["PATH"]}')]
        for p in self.patches:
            p.start()
        self.library = library

    def tearDown(self):
        for p in reversed(self.patches):
            p.stop()
        self.tmp.cleanup()

    def _clone(self, name):
        path = self.base / name
        self.git('clone', '-q', str(self.origin), str(path), cwd=self.base)
        self.git('config', 'user.email', 't@example.com', cwd=path); self.git('config', 'user.name', 't', cwd=path)
        if not self.git('branch', '--show-current', cwd=path).strip():
            self.git('checkout', '-q', '-b', 'main', cwd=path)
        return path

    def _write(self, rel, text, root=None):
        path = (root or self.root) / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def _show(self, ref, rel):
        return self.git('show', f'{ref}:{rel}', cwd=self.origin)

    def _pr_state(self):
        return json.loads(self.prs.read_text()) if self.prs.exists() else {}

    def _set_pr(self, branch, **fields):
        prs = self._pr_state(); prs[branch].update(fields); self.prs.write_text(json.dumps(prs))

    def _merge(self, branch):
        """模拟 GitHub 的 squash 合并，并把 PR 记成已合并。"""
        other = self._clone('gh-' + uuid.uuid4().hex[:6])
        self.git('merge', '-q', '--squash', f'origin/{branch}', cwd=other)
        self.git('commit', '-q', '-m', 'squash', cwd=other); self.git('push', '-q', 'origin', 'main', cwd=other)
        self._set_pr(branch, state='MERGED')

    def _push_from(self, root, rel, text):
        self._write(rel, text, root)
        self.git('add', '-A', cwd=root); self.git('commit', '-q', '-m', 'elsewhere', cwd=root); self.git('push', '-q', 'origin', 'main', cwd=root)

    def test_snapshot_opens_its_own_data_pr_and_requests_auto_merge(self):
        self._write('forge/data/ledger.jsonl', 'a\nb\n')
        self._write('app.py', 'x = 2\n')
        result = self.library.snapshot('two entries')
        self.assertTrue(result['ok'] and result['committed'] and result['published'] and result['auto_merge'], result)
        self.assertTrue(result['branch'].startswith('data/snapshot-'))
        self.assertEqual(self._show(result['branch'], 'forge/data/ledger.jsonl'), 'a\nb\n')
        self.assertEqual(self._show(result['branch'], 'app.py'), 'x = 1\n')  # 代码改动没被带进快照
        self.assertEqual(self.git('rev-parse', 'main', cwd=self.origin), self.git('rev-parse', 'HEAD~1'))  # main 没被直接推
        self.assertIn('--auto --squash', self.log.read_text())

    def test_snapshot_refuses_when_local_main_has_unreviewed_code(self):
        self._write('app.py', 'x = 3\n')
        self.git('commit', '-q', '-am', 'code on main')
        result = self.library.snapshot('data')
        self.assertFalse(result['ok'])
        self.assertEqual(result['paths'], ['app.py'])

    def test_include_only_takes_result_paths(self):
        for path in ['app.py', 'forge/data/../../app.py', 'lean/Mathlib2Evil.py']:
            self.assertFalse(self.library.snapshot('x', include=[path])['ok'], path)

    def test_snapshot_off_main_commits_locally(self):
        self.git('checkout', '-q', '-b', 'upgrade')
        self._write('forge/data/ledger.jsonl', 'a\nb\n')
        result = self.library.snapshot('upgrade data')
        self.assertTrue(result['ok'] and result['committed'] and not result['published'], result)
        self.assertFalse(self.log.exists())

    def test_second_snapshot_updates_its_open_pr(self):
        self._write('forge/data/ledger.jsonl', 'a\nb\n'); first = self.library.snapshot('one')
        self._write('forge/data/ledger.jsonl', 'a\nb\nc\n'); second = self.library.snapshot('two')
        self.assertTrue(second['updated_existing_pr'], second)
        self.assertEqual(first['branch'], second['branch'])
        self.assertEqual(self.log.read_text().count('pr create'), 1)
        self.assertEqual(self._show(second['branch'], 'forge/data/ledger.jsonl'), 'a\nb\nc\n')

    def test_after_its_pr_merges_the_next_snapshot_opens_a_new_one(self):
        self._write('forge/data/ledger.jsonl', 'a\nb\n'); first = self.library.snapshot('one')
        self._merge(first['branch'])
        self._write('forge/data/ledger.jsonl', 'a\nb\nc\n'); second = self.library.snapshot('two')
        self.assertTrue(second['ok'] and second['published'] and not second['updated_existing_pr'], second)
        self.assertNotEqual(first['branch'], second['branch'])
        self._merge(second['branch'])
        self.assertTrue(self.library.sync()['ok'])
        self.assertEqual(self.git('show', 'HEAD:forge/data/ledger.jsonl'), 'a\nb\nc\n')

    def test_pr_merged_between_check_and_push_gets_a_new_pr(self):
        self._write('forge/data/ledger.jsonl', 'a\nb\n'); first = self.library.snapshot('one')
        self._set_pr(first['branch'], flip_after=1)  # 第一次查询还开着，推送后再查已合并
        self._write('forge/data/ledger.jsonl', 'a\nb\nc\n'); second = self.library.snapshot('two')
        self.assertTrue(second['published'] and second['branch'] != first['branch'], second)
        self.assertEqual(self._pr_state()[second['branch']]['state'], 'OPEN')

    def test_another_checkouts_snapshot_pr_is_left_alone(self):
        self._write('forge/data/ledger.jsonl', 'a\nA\n'); mine = self.library.snapshot('machine A')
        other = self._clone('machine-b')
        self.root_patch.stop()
        with mock.patch('forge.leanrun.ROOT', other):
            self._write('forge/data/helpers.json', '{}', other)
            theirs = self.library.snapshot('machine B', include=['forge/data/helpers.json'])
        self.root_patch.start()
        self.assertTrue(theirs['published'] and theirs['branch'] != mine['branch'], theirs)
        self.assertEqual(self._show(mine['branch'], 'forge/data/ledger.jsonl'), 'a\nA\n')

    def test_hand_written_data_pr_is_left_alone(self):
        self.git('push', '-q', 'origin', 'main:refs/heads/data/audit-b1-results')
        before = self.git('rev-parse', 'data/audit-b1-results', cwd=self.origin)
        self._write('forge/data/ledger.jsonl', 'a\nb\n')
        result = self.library.snapshot('mine')
        self.assertTrue(result['published'] and result['branch'].startswith('data/snapshot-'), result)
        self.assertEqual(self.git('rev-parse', 'data/audit-b1-results', cwd=self.origin), before)

    def test_a_task_claimed_elsewhere_is_a_conflict_not_undone(self):
        self._write('forge/data/tasks/open/x.json', '{"v":0}')
        self.git('add', '-A'); self.git('commit', '-q', '-m', 'x'); self.git('push', '-q', 'origin', 'main')
        (self.root / 'forge/data/tasks/open/x.json').unlink(); self.library.snapshot('claim x', publish=False)
        self._write('forge/data/tasks/open/x.json', '{"v":1}'); self.library.snapshot('release x', publish=False)
        other = self._clone('claimer')
        (other / 'forge/data/tasks/open/x.json').unlink()
        self._push_from(other, 'forge/data/tasks/claimed/x.json', '{"v":0}')
        result = self.library.snapshot('publish')
        self.assertFalse(result['ok'], result)
        self.assertIn('forge/data/tasks/open/x.json', result['paths'])

    def test_auto_merge_is_requested_again_on_an_open_pr(self):
        self._write('forge/data/ledger.jsonl', 'a\nb\n'); first = self.library.snapshot('one')
        self._set_pr(first['branch'], autoMergeRequest=None)  # 自动合并被取消或当初没开成
        self._write('forge/data/ledger.jsonl', 'a\nb\nc\n'); second = self.library.snapshot('two')
        self.assertTrue(second['auto_merge'], second)
        self.assertEqual(self.log.read_text().count('--auto --squash'), 2)

    def test_push_refuses_to_overwrite_a_branch_changed_by_someone_else(self):
        self._write('forge/data/ledger.jsonl', 'a\nb\n'); first = self.library.snapshot('one')
        other = self._clone('intruder')
        self.git('fetch', '-q', 'origin', first['branch'], cwd=other)
        self.git('checkout', '-q', '-b', 'x', 'FETCH_HEAD', cwd=other)
        self._write('forge/data/extra.txt', 'theirs', other)
        self.git('add', '-A', cwd=other); self.git('commit', '-q', '-m', 'e', cwd=other)
        self.git('push', '-q', 'origin', f'x:{first["branch"]}', cwd=other)
        self._write('forge/data/ledger.jsonl', 'a\nb\nc\n'); second = self.library.snapshot('two')
        self.assertFalse(second['ok'], second)
        self.assertEqual(self._show(first['branch'], 'forge/data/extra.txt'), 'theirs')

    def test_sync_fast_forwards_and_keeps_uncommitted_data(self):
        self._push_from(self._clone('other'), 'app.py', 'x = 9\n')
        self._write('forge/data/ledger.jsonl', 'a\nunsaved\n')
        self.assertTrue(self.library.sync()['ok'])
        self.assertEqual((self.root / 'app.py').read_text(), 'x = 9\n')
        self.assertEqual((self.root / 'forge/data/ledger.jsonl').read_text(), 'a\nunsaved\n')

    def test_sync_waits_while_data_is_unmerged(self):
        self._write('forge/data/ledger.jsonl', 'a\nb\n'); self.library.snapshot('local only', publish=False)
        self.assertFalse(self.library.sync()['ok'])

    def test_sync_after_merge_even_if_the_file_changed_again_upstream(self):
        self._write('forge/data/ledger.jsonl', 'a\nb\n'); first = self.library.snapshot('one')
        self._merge(first['branch'])
        self._push_from(self._clone('later'), 'forge/data/ledger.jsonl', 'a\nb\nlater\n')
        result = self.library.sync()
        self.assertTrue(result['ok'], result)
        self.assertEqual((self.root / 'forge/data/ledger.jsonl').read_text(), 'a\nb\nlater\n')

    def test_deleted_include_and_emptied_directory_are_committed(self):
        self._write('reports/r.txt', 'r'); self._write('forge/data/tasks/t.json', '{}')
        self.assertTrue(self.library.snapshot('add', include=['reports/r.txt'], publish=False)['committed'])
        (self.root / 'reports/r.txt').unlink(); (self.root / 'forge/data/tasks/t.json').unlink()
        result = self.library.snapshot('remove', include=['reports/r.txt'], publish=False)
        self.assertTrue(result['ok'] and result['committed'], result)
        self.assertEqual(self.git('status', '--short', '--', 'reports', 'forge/data'), '')
        result = self.library.snapshot('nothing', include=['reports/r.txt'], publish=False)
        self.assertTrue(result['ok'] and not result['committed'], result)


class PortfolioCopyTests(unittest.TestCase):
    """组合拆解的抄写检测：子引理抄来的，用到它的题也不算解出；自己上一次留下的引理不算来源。"""

    PROOF = '\n'.join(f'  have h{i} : some_long_fact_number_{i} = other_side_{i} := by ring_nf' for i in range(8))

    def setUp(self):
        from forge import portfolio
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.root = root = Path(self.tmp.name)
        stack = contextlib.ExitStack(); self.addCleanup(stack.close)
        for patch in (mock.patch.object(portfolio, 'STATE_DIR', root / 'scratch' / 'portfolio'),
                      mock.patch.object(portfolio, 'LEGACY_STATE_DIR', root / 'legacy' / 'portfolio'),
                      mock.patch.object(portfolio, 'SCRATCH', root / 'scratch'), mock.patch.object(portfolio, 'DATA', root / 'data'),
                      mock.patch('forge.scheduler.SCRATCH', root / 'scratch'), mock.patch('forge.scheduler.RUNS', root / 'runs'),
                      mock.patch('forge.provenance.SCRATCH', root / 'scratch'), mock.patch('forge.provenance.LEGACY', ()),
                        mock.patch('forge.provenance.checkouts', lambda: [Path('/nonexistent-checkout')]),
                      mock.patch.object(portfolio.bench, 'load', return_value=[dict(name='p', statement=': True')])):
            stack.enter_context(patch)
        self.portfolio = portfolio
        self.runner = portfolio.Portfolio('pf-now', workers=1, max_tasks=1000, dry_run=True)
        self.runner.items = {'p': dict(name='p', statement=': True')}
        self.runner.set_name, self.runner.file_lock = 's', threading.Lock()
        self.runner.state = dict(run='pf-now', problems={'p': dict(set='s', solved_by=None, dags={
            'd1': dict(skeleton='', holes=[dict(lemma='L', args=[])], status='assembling')})},
            lemmas={'L': dict(set='s', problem='p', statement='True', hash='h', status='proved', dags=['d1'], body='x')})

    def _old(self, rel):
        path = self.root / 'scratch' / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(self.PROOF)
        old = time.time() - 3600
        os.utime(path, (old, old))

    def test_own_earlier_files_are_not_sources_but_other_runs_are(self):
        self._old('agents/pf-now/pf-now-w1/L.proved.lean')
        self.assertIsNone(self.runner._copy_of(self.PROOF))
        self._old('agents/pf-other/w1/L.proved.lean')
        self.assertIn('pf-other', self.runner._copy_of(self.PROOF))

    def test_own_drafts_in_another_worktree_are_not_sources(self):
        other = self.root / 'other-checkout'
        own = other / 'forge' / 'data' / 'staging' / 'agents' / 'pf-now' / 'w1' / 'L.final.lean'
        state = other / 'forge' / 'data' / 'staging' / 'portfolio' / 'pf-now.json'
        foreign = other / 'forge' / 'data' / 'staging' / 'agents' / 'pf-other' / 'w1' / 'L.final.lean'
        for path in (own, state):
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(self.PROOF if path.suffix == '.lean' else json.dumps(dict(x=self.PROOF)))
            os.utime(path, (time.time() - 3600,) * 2)
        with mock.patch('forge.provenance.checkouts', lambda: [Path('/nonexistent-checkout'), other]):
            self.assertIsNone(self.runner._copy_of(self.PROOF))   # 同名轮次在别的检出里留下的是自己的
            foreign.parent.mkdir(parents=True)
            foreign.write_text(self.PROOF)
            os.utime(foreign, (time.time() - 3600,) * 2)
            self.assertIn('pf-other', self.runner._copy_of(self.PROOF))

    def test_a_problem_using_a_copied_lemma_is_not_solved(self):
        self.runner.state['lemmas']['L']['copied'] = '/old/x.lean'
        def check(set_name, problem, body, run, agent, before=None, exclude=(), inherited=None):
            return dict(ok=True, kind='proved', solved=True, reason='通过',
                        copy=dict(copied=bool(inherited), source=inherited, overlap=0.0))
        with mock.patch.object(self.portfolio.bench, 'check', side_effect=check), \
                mock.patch.object(self.portfolio, 'assemble_body', return_value='theorem p : True := trivial'):
            self.runner._assemble('a1', 'p', 'd1')
        d = self.runner.state['problems']['p']['dags']['d1']
        self.assertEqual((d['status'], d['copied']), ('copied', 'lemma:L'))
        self.assertIsNone(self.runner.state['problems']['p']['solved_by'])
        self.assertEqual(self.runner.records[-1]['outcome'], 'copied')

    def test_a_proved_lemma_is_checked(self):
        self._old('agents/pf-other/w1/L.final.lean')
        info = self.runner.state['lemmas']['L']
        info.update(status='open', attempts=0)
        self.runner.state['problems']['p']['dags']['d1']['status'] = 'open'   # 引理还有图在用，才会去证
        self.runner.lemma_seconds, self.runner.lemma_attempts = 60, 1
        def invoke(prompt, agent, seconds=None):
            (self.runner.scratch / agent).mkdir(parents=True, exist_ok=True)
            (self.runner.scratch / agent / 'L.lean').write_text('theorem L : True := by\n' + self.PROOF)
            return 0, '', 0, False
        with mock.patch.object(self.runner, '_invoke', side_effect=invoke), \
                mock.patch('forge.verify.check_submission', return_value=dict(ok=True, kind='proved', reason='通过')), \
                mock.patch.object(self.runner, '_resolved'):
            self.runner._lemma('a1', 'p', 'L')
        self.assertIn('pf-other', info['copied'])


class PortfolioMainLastTests(unittest.TestCase):
    def test_main_last_moves_the_main_theorem_after_its_helpers(self):
        from forge.portfolio import main_last
        from forge.statement import analyse_submission
        body = ('open Nat\n\ntheorem p_d1_h1 : 1 = 1 := by\n  exact p_d1_h1_aux\n\n'
                '-- helper\ntheorem p_d1_h1_aux : 1 = 1 := by\n  rfl\n')
        fixed = main_last(body, 'p_d1_h1')
        self.assertEqual(analyse_submission(fixed, 'p_d1_h1'), ['p_d1_h1_aux', 'p_d1_h1'])
        self.assertTrue(fixed.startswith('open Nat'))
        ok = 'theorem p_d1_h1_aux : 1 = 1 := rfl\ntheorem p_d1_h1 : 1 = 1 := p_d1_h1_aux\n'
        self.assertEqual(main_last(ok, 'p_d1_h1'), ok)  # 已经合规的不动
        commented = 'theorem p_d1_h1_aux : 1 = 1 := rfl\ntheorem p_d1_h1 : 1 = 1 := p_d1_h1_aux\n/-\nnotes at column 0\n-/\n'
        self.assertEqual(main_last(commented, 'p_d1_h1'), commented)  # 结尾的块注释不算声明，合规的文件原样保留
        late = 'theorem p_d1_h1 : 1 = 1 := p_d1_h1_aux\n/-\nnotes\n-/\ntheorem p_d1_h1_aux : 1 = 1 := rfl\n'
        self.assertEqual(analyse_submission(main_last(late, 'p_d1_h1'), 'p_d1_h1'), ['p_d1_h1_aux', 'p_d1_h1'])
        dis = 'theorem p_d1_h1_disproof : ¬ (1 = 2) := by\n  decide\ntheorem p_d1_h1_aux : True := trivial\n'
        self.assertEqual(analyse_submission(main_last(dis, 'p_d1_h1'), 'p_d1_h1', disproof=True)[-1], 'p_d1_h1_disproof')


class PortfolioSplitTests(unittest.TestCase):
    def test_stuck_lemma_is_split_assembled_and_unblocks_the_problem(self):
        from forge import portfolio
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        (root / 'pf').mkdir()
        state = dict(run='t-s', problems=dict(p=dict(set='s', solved_by=None, dags=dict(
            d1=dict(skeleton='theorem p : True := by\n  exact (by sorry)', holes=[dict(lemma='p_d1_h1', args=[])],
                    status='open', planner='w')))),
            lemmas=dict(p_d1_h1=dict(set='s', problem='p', statement='True ∧ True', hash='h', status='unsolved', dags=['d1'],
                                     attempts=2)))
        (root / 'pf' / 't-s.json').write_text(json.dumps(state))
        bodies = []

        def fake_submission(task, body, **kw):
            bodies.append((task['name'], body))
            return dict(ok=True, kind='proved')
        with mock.patch.object(portfolio, 'STATE_DIR', root / 'pf'), mock.patch('forge.scheduler.RUNS', root / 'runs'), \
             mock.patch('forge.scheduler.DATA', root), mock.patch.object(portfolio.bench, 'load', return_value=[dict(name='p', statement=': True')]), \
             mock.patch('forge.verify.check_sketch', return_value=dict(ok=True, holes=[dict(statement='True', hash='h2', args=[])])), \
             mock.patch('forge.verify.check_submission', side_effect=fake_submission), \
             mock.patch.object(portfolio.bench, 'check', return_value=dict(ok=True, solved=True)):
            runner = portfolio.Portfolio('t-s', workers=2, max_tasks=1000, dry_run=True)

            def fake_invoke(prompt, agent, **kw):
                folder = runner.scratch / agent
                if 'p_d1_h1.d1.sketch.lean' in prompt:
                    (folder / 'p_d1_h1.d1.sketch.lean').write_text('theorem p_d1_h1 : True := by\n  exact (by sorry)')
                if 'p_d1_h1_d1_h1.lean' in prompt:
                    (folder / 'p_d1_h1_d1_h1.lean').write_text('theorem p_d1_h1_d1_h1 : True := trivial')
                return 0, '', 0, False
            runner._invoke = fake_invoke
            result = runner.run_portfolio('s', ['p'], k=1, split=1)
        lemmas = runner.state['lemmas']
        self.assertEqual(lemmas['p_d1_h1_d1_h1']['parents'], [['p_d1_h1', 'd1']])
        self.assertEqual(lemmas['p_d1_h1']['status'], 'proved')
        self.assertEqual(lemmas['p_d1_h1']['proved_by'], 'd1')
        # 拼出的引理证明：子引理改名成 `<父引理>_aux…`，主定理在最后
        name, body = next(b for b in bodies if b[0] == 'p_d1_h1')
        from forge.statement import analyse_submission
        self.assertEqual(analyse_submission(body, 'p_d1_h1'), ['p_d1_h1_aux_d1_h1', 'p_d1_h1'])
        self.assertNotIn('sorry', body)
        self.assertEqual(result['solved'], 1)

    def test_a_split_that_restates_the_lemma_is_rejected(self):
        from forge import portfolio
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        (root / 'pf').mkdir()
        state = dict(run='t-s', problems=dict(p=dict(set='s', solved_by=None, dags=dict(
            d1=dict(skeleton='theorem p : True := by\n  exact (by sorry)', holes=[dict(lemma='p_d1_h1', args=[])],
                    status='open', planner='w')))),
            lemmas=dict(p_d1_h1=dict(set='s', problem='p', statement='True ∧ True', hash='h', status='unsolved', dags=['d1'],
                                     attempts=2)))
        (root / 'pf' / 't-s.json').write_text(json.dumps(state))
        bodies = []

        def fake_submission(task, body, **kw):
            bodies.append((task['name'], body))
            return dict(ok=True, kind='proved')
        with mock.patch.object(portfolio, 'STATE_DIR', root / 'pf'), mock.patch('forge.scheduler.RUNS', root / 'runs'), \
             mock.patch('forge.scheduler.DATA', root), mock.patch.object(portfolio.bench, 'load', return_value=[dict(name='p', statement=': True')]), \
             mock.patch('forge.verify.check_sketch', return_value=dict(ok=True, holes=[dict(statement='True  ∧ True', hash='h2', args=[])])), \
             mock.patch('forge.verify.check_submission', side_effect=fake_submission), \
             mock.patch.object(portfolio.bench, 'check', return_value=dict(ok=True, solved=True)):
            runner = portfolio.Portfolio('t-s', workers=2, max_tasks=1000, dry_run=True)

            def fake_invoke(prompt, agent, **kw):
                folder = runner.scratch / agent
                if 'p_d1_h1.d1.sketch.lean' in prompt:
                    (folder / 'p_d1_h1.d1.sketch.lean').write_text('theorem p_d1_h1 : True := by\n  exact (by sorry)')
                if 'p_d1_h1_d1_h1.lean' in prompt:
                    (folder / 'p_d1_h1_d1_h1.lean').write_text('theorem p_d1_h1_d1_h1 : True := trivial')
                return 0, '', 0, False
            runner._invoke = fake_invoke
            result = runner.run_portfolio('s', ['p'], k=1, split=1)
        self.assertNotIn('p_d1_h1_d1_h1', runner.state['lemmas'])
        self.assertEqual(runner.state['lemmas']['p_d1_h1']['splits']['d1']['status'], 'failed')  # 记下失败，接着跑不再重派
        self.assertEqual(result['solved'], 0)


class PortfolioRetryTests(unittest.TestCase):
    def test_a_retry_sees_the_previous_failed_attempt(self):
        from forge import portfolio
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        (root / 'pf').mkdir()
        state = dict(run='t-p', problems=dict(p=dict(set='s', solved_by=None, dags=dict(
            d1=dict(skeleton='', holes=[dict(lemma='l1', args=[])], status='open', planner='w')))),
            lemmas=dict(l1=dict(set='s', problem='p', statement='True', hash='h', status='open', dags=['d1'])))
        (root / 'pf' / 't-p.json').write_text(json.dumps(state))
        prompts = []
        with mock.patch.object(portfolio, 'STATE_DIR', root / 'pf'), mock.patch('forge.scheduler.RUNS', root / 'runs'), \
             mock.patch('forge.scheduler.DATA', root), mock.patch.object(portfolio.bench, 'load', return_value=[dict(name='p', statement=': True')]), \
             mock.patch('forge.verify.check_submission', return_value=dict(ok=False, reason='Lean 报错', errors=[dict(line=1, message='boom')])):
            runner = portfolio.Portfolio('t-p', workers=1, max_tasks=1000, dry_run=True)

            def fake_invoke(prompt, agent, **kw):
                prompts.append(prompt)
                (runner.scratch / agent / 'l1.lean').write_text(f'theorem l1 : True := by\n  attempt{len(prompts)}')
                return 0, '', 0, False
            runner._invoke = fake_invoke
            runner.run_portfolio('s', ['p'], k=1)
        self.assertEqual(len(prompts), 2)
        self.assertNotIn('earlier agent', prompts[0])
        self.assertIn('earlier agent', prompts[1])
        self.assertIn('boom', prompts[1])
        kept = Path(runner.state['lemmas']['l1']['last_attempt']['file'])
        self.assertIn('attempt2', kept.read_text())  # 最新一次的失败提交
        self.assertIn('attempt1', (kept.parent / 'l1.1.lean').read_text())

    def _split_state(self, root, sub_status):
        state = dict(run='t-k', problems=dict(p=dict(set='s', solved_by=None, dags=dict(
            d1=dict(skeleton='theorem p : True := by\n  exact (by sorry)', holes=[dict(lemma='p_d1_h1', args=[])],
                    status='open', planner='w')))),
            lemmas=dict(p_d1_h1=dict(set='s', problem='p', statement='True ∧ True', hash='h', status='unsolved', dags=['d1'],
                                     attempts=2, splits=dict(
                                         d1=dict(skeleton='theorem p_d1_h1 : True ∧ True := by\n  exact ⟨by sorry, trivial⟩',
                                                 holes=[dict(lemma='p_d1_h1_d1_h1', args=[])], status='open', planner='w'),
                                         d2=dict(skeleton='', holes=[], status='failed', planner='w'))),
                        p_d1_h1_d1_h1=dict(set='s', problem='p', statement='True', hash='h2', status=sub_status, dags=[],
                                           attempts=0, depth=1, parents=[['p_d1_h1', 'd1']])))
        (root / 'pf').mkdir()
        (root / 'pf' / 't-k.json').write_text(json.dumps(state))

    def test_disproved_part_kills_only_its_sub_dag_and_resume_skips_failed_planners(self):
        from forge import portfolio
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        self._split_state(root, 'open')
        seen = []
        with mock.patch.object(portfolio, 'STATE_DIR', root / 'pf'), mock.patch('forge.scheduler.RUNS', root / 'runs'), \
             mock.patch('forge.scheduler.DATA', root), mock.patch.object(portfolio.bench, 'load', return_value=[dict(name='p', statement=': True')]), \
             mock.patch('forge.verify.check_submission', return_value=dict(ok=True, kind='disproved')):
            runner = portfolio.Portfolio('t-k', workers=1, max_tasks=1000, dry_run=True)
            real = runner._lemma
            def lemma(agent, p, name):
                seen.append(name)
                (runner.scratch / agent / f'{name}.lean').parent.mkdir(parents=True, exist_ok=True)
                runner._invoke = lambda prompt, agent, **kw: ((runner.scratch / agent / f'{name}.lean').write_text(
                    f'theorem {name}_disproof : ¬ True := by\n  simp'), (0, '', 0, False))[1]
                real(agent, p, name)
            runner._lemma = lemma
            runner._split_sketch = lambda *a: seen.append(('split_sketch',) + a[1:])
            runner.run_portfolio('s', ['p'], k=1, split=2)
        self.assertEqual(seen, ['p_d1_h1_d1_h1'])  # 失败过的规划者 d2 不重派
        lemmas = runner.state['lemmas']
        self.assertEqual(lemmas['p_d1_h1']['splits']['d1']['status'], 'dead')
        self.assertEqual(runner.state['problems']['p']['dags']['d1']['status'], 'open')  # 题目的图不受牵连
        self.assertEqual(lemmas['p_d1_h1']['status'], 'unsolved')

    def test_resume_assembles_a_split_whose_parts_were_already_proved(self):
        from forge import portfolio
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        self._split_state(root, 'proved')
        state = json.loads((root / 'pf' / 't-k.json').read_text())
        state['lemmas']['p_d1_h1_d1_h1']['body'] = 'theorem p_d1_h1_d1_h1 : True := trivial'
        state['lemmas']['p_d1_h1']['splits']['d1']['status'] = 'assembling'  # 上次拼到一半被打断
        (root / 'pf' / 't-k.json').write_text(json.dumps(state))
        with mock.patch.object(portfolio, 'STATE_DIR', root / 'pf'), mock.patch('forge.scheduler.RUNS', root / 'runs'), \
             mock.patch('forge.scheduler.DATA', root), mock.patch.object(portfolio.bench, 'load', return_value=[dict(name='p', statement=': True')]), \
             mock.patch('forge.verify.check_submission', return_value=dict(ok=True, kind='proved')), \
             mock.patch.object(portfolio.bench, 'check', return_value=dict(ok=True, solved=True)):
            runner = portfolio.Portfolio('t-k', workers=1, max_tasks=1000, dry_run=True)
            runner._invoke = lambda *a, **kw: self.fail('no agent should be needed')
            result = runner.run_portfolio('s', ['p'], k=1, split=2)
        self.assertEqual(runner.state['lemmas']['p_d1_h1']['status'], 'proved')
        self.assertEqual(result['solved'], 1)

    def test_failed_mechanical_lemma_assembly_falls_back_to_an_agent(self):
        from forge import portfolio
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        self._split_state(root, 'proved')
        state = json.loads((root / 'pf' / 't-k.json').read_text())
        state['lemmas']['p_d1_h1_d1_h1']['body'] = 'theorem p_d1_h1_d1_h1 : True := trivial'
        (root / 'pf' / 't-k.json').write_text(json.dumps(state))
        verdicts = [dict(ok=False, reason='mechanical: type mismatch'), dict(ok=True, kind='proved')]
        with mock.patch.object(portfolio, 'STATE_DIR', root / 'pf'), mock.patch('forge.scheduler.RUNS', root / 'runs'), \
             mock.patch('forge.scheduler.DATA', root), mock.patch.object(portfolio.bench, 'load', return_value=[dict(name='p', statement=': True')]), \
             mock.patch('forge.verify.check_submission', side_effect=lambda *a, **kw: verdicts.pop(0)), \
             mock.patch.object(portfolio.bench, 'check', return_value=dict(ok=True, solved=True)):
            runner = portfolio.Portfolio('t-k', workers=1, max_tasks=1000, dry_run=True)
            prompts = []

            def fake_invoke(prompt, agent, **kw):
                prompts.append(prompt)
                (runner.scratch / agent / 'p_d1_h1.d1.final.lean').write_text(
                    'theorem p_d1_h1_aux_d1_h1 : True := trivial\ntheorem p_d1_h1 : True ∧ True := ⟨p_d1_h1_aux_d1_h1, trivial⟩')
                return 0, '', 0, False
            runner._invoke = fake_invoke
            result = runner.run_portfolio('s', ['p'], k=1, split=2)
        self.assertEqual(len(prompts), 1)
        self.assertIn('mechanical: type mismatch', prompts[0])
        self.assertEqual(runner.state['lemmas']['p_d1_h1']['status'], 'proved')
        self.assertEqual(runner.state['lemmas']['p_d1_h1']['splits']['d1']['status'], 'solved')
        self.assertEqual(result['solved'], 1)

    def test_queue_prefers_the_lemma_closest_to_finishing_a_problem_dag(self):
        from forge import portfolio
        runner = portfolio.Portfolio('t-q', workers=1, max_tasks=1000, dry_run=True)
        runner.state = dict(problems=dict(p=dict(solved_by=None, dags=dict(
            d1=dict(status='open', holes=[dict(lemma='a'), dict(lemma='b'), dict(lemma='c')]),
            d2=dict(status='open', holes=[dict(lemma='x'), dict(lemma='y')])))),
            lemmas=dict(a=dict(problem='p', status='open', dags=['d1']), b=dict(problem='p', status='open', dags=['d1']),
                        c=dict(problem='p', status='open', dags=['d1']), x=dict(problem='p', status='unsolved', dags=['d2'],
                        splits=dict(d1=dict(status='open', holes=[dict(lemma='x_d1_h1')]))),
                        y=dict(problem='p', status='proved', dags=['d2']),
                        x_d1_h1=dict(problem='p', status='open', dags=[], parents=[['x', 'd1']])))
        runner.queue = [('lemma', 'p', 'a'), ('split_sketch', 'p', 'x', 2), ('lemma', 'p', 'x_d1_h1'), ('sketch', 'p', 3)]
        runner.busy, runner.stop_reason = 0, None
        order = [runner._take() for _ in range(4)]
        # 新骨架最先；x 的唯一子引理证出就能拼完 d2（距离 0）；再拆 x 次之；a 所在的 d1 还差两条
        self.assertEqual(order, [('sketch', 'p', 3), ('lemma', 'p', 'x_d1_h1'), ('split_sketch', 'p', 'x', 2), ('lemma', 'p', 'a')])


class MemoryGateTests(unittest.TestCase):
    def test_no_new_task_starts_while_free_memory_is_below_the_gate(self):
        from forge import scheduler
        runner = scheduler.Scheduler('t-mem', workers=1, max_tasks=10, dry_run=True, min_free_memory=30)
        readings = iter([12, 20, 45])
        with mock.patch.object(scheduler, 'free_memory_percent', side_effect=lambda: next(readings)), \
             mock.patch.object(scheduler.time, 'sleep') as sleep:
            self.assertTrue(runner._may_start())
        self.assertEqual(sleep.call_count, 2)  # 12%、20% 时等，45% 时放行
        self.assertEqual([e['event'] for e in runner.events], ['memory_wait'])
        self.assertEqual(runner.started, 1)

    def test_gate_off_or_unreadable_memory_never_blocks(self):
        from forge import scheduler
        off = scheduler.Scheduler('t-mem0', workers=1, max_tasks=10, dry_run=True)
        unreadable = scheduler.Scheduler('t-mem1', workers=1, max_tasks=10, dry_run=True, min_free_memory=30)
        with mock.patch.object(scheduler, 'free_memory_percent', return_value=None) as reading, \
             mock.patch.object(scheduler.time, 'sleep', side_effect=AssertionError('should not wait')):
            self.assertTrue(off._may_start())
            self.assertTrue(unreadable._may_start())
        self.assertEqual(reading.call_count, 1)  # 关闭时根本不读

    def test_waiting_ends_when_the_run_is_stopped(self):
        from forge import scheduler
        runner = scheduler.Scheduler('t-mem2', workers=1, max_tasks=10, dry_run=True, min_free_memory=30)
        def stop(_):
            runner.stop_reason = '手动停止'
        with mock.patch.object(scheduler, 'free_memory_percent', return_value=5), \
             mock.patch.object(scheduler.time, 'sleep', side_effect=stop):
            self.assertFalse(runner._may_start())

    def test_recent_starts_are_reserved_so_waiting_workers_do_not_all_pass(self):
        from forge import scheduler
        runner = scheduler.Scheduler('t-mem3', workers=6, max_tasks=10, dry_run=True, min_free_memory=30)
        # 空闲 55%、每个刚开始的任务预留 6%：55-0 … 55-24=31 都放行（5 个），第六个 55-30=25 < 30 要等
        with mock.patch.object(scheduler, 'free_memory_percent', return_value=55), \
             mock.patch.object(scheduler.time, 'sleep', side_effect=lambda _: setattr(runner, 'stop_reason', 'x')):
            passed = [runner._may_start() for _ in range(6)]
        self.assertEqual(passed, [True] * 5 + [False])

    def test_out_of_range_gate_is_rejected(self):
        from forge import scheduler
        with self.assertRaises(ValueError):
            scheduler.Scheduler('t-mem4', workers=1, max_tasks=1, dry_run=True, min_free_memory=300)
        from forge.__main__ import main
        with self.assertRaises(SystemExit):
            main(['portfolio', '--run', 'x', '--bench', 's', '--problems', 'p', '--min-free-memory', '300'])

    def test_portfolio_cli_passes_the_gate_to_the_scheduler(self):
        from forge import __main__ as cli, portfolio
        seen = {}
        class Fake(portfolio.Portfolio):
            def __init__(self, *a, **kw):
                seen.update(kw)
                raise SystemExit(0)
        with mock.patch.object(portfolio, 'Portfolio', Fake):
            with self.assertRaises(SystemExit):
                cli.main(['portfolio', '--run', 'x', '--bench', 's', '--problems', 'p', '--min-free-memory', '30'])
        self.assertEqual(seen['min_free_memory'], 30)

    def test_free_memory_reading_is_cached_briefly(self):
        from forge import scheduler
        scheduler._memory_cache[:] = [0.0, None]
        with mock.patch.object(scheduler, '_read_free_memory', return_value=40) as read:
            self.assertEqual(scheduler.free_memory_percent(), 40)
            self.assertEqual(scheduler.free_memory_percent(), 40)
        self.assertEqual(read.call_count, 1)
        scheduler._memory_cache[:] = [0.0, None]


class ShardImportTests(unittest.TestCase):
    ROWS = [dict(name='a', task='a', shard='S0001', library_deps=[], helpers=['a_aux']),
            dict(name='b', task='b', shard='S0002', library_deps=[], helpers=[]),
            dict(name='c', task='c', shard='S0003', library_deps=['a_aux', 'c0'], helpers=[]),
            dict(name='c0', task='c0', shard='S0003', library_deps=[], helpers=[])]

    def test_shards_import_only_the_shards_their_theorems_use(self):
        from forge import library
        # c 用到 S0001 的辅助引理和同分片的 c0：只导入 S0001，不导入 S0002，也不导入自己
        self.assertEqual(library.shard_imports(self.ROWS), {'S0001': set(), 'S0002': set(), 'S0003': {'S0001'}})

    def test_with_imports_adds_missing_imports_after_mathlib_and_keeps_existing(self):
        from forge import library
        text = '/- 分片 -/\nimport Mathlib\nimport Mathlib2.Shard.S0002\nset_option x 1\nnamespace Mathlib2\n\nend Mathlib2\n'
        out = library._with_imports(text, 'S0005', {'S0001', 'S0005'})
        self.assertEqual(out, '/- 分片 -/\nimport Mathlib\nimport Mathlib2.Shard.S0001\nimport Mathlib2.Shard.S0002\n'
                              'set_option x 1\nnamespace Mathlib2\n\nend Mathlib2\n')
        self.assertEqual(library._with_imports(out, 'S0005', {'S0001'}), out)  # 再跑一遍不变

    def test_rollback_journal_still_matches_after_an_admission_added_imports(self):
        from forge import library
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        shard = root / 'S0003.lean'
        original = '/- s -/\nimport Mathlib\nset_option x 1\nnamespace Mathlib2\n\nend Mathlib2\n'
        grown = library._with_imports(original, 'S0003', {'S0001'}).replace(
            'end Mathlib2\n', '-- forge:entry c kind=proved origin=\nsection\ntheorem c : True := trivial\nend\n\nend Mathlib2\n')
        shard.write_text(grown, encoding='utf-8')
        ledger = root / 'ledger.jsonl'
        ledger.write_text(json.dumps(dict(task='c')) + '\n', encoding='utf-8')
        journal = dict(names=['c'], ledger_size=0, ledger_digest=hashlib.sha256(b'').hexdigest(), shards={str(shard): original})
        with mock.patch.object(library, 'LEDGER', ledger):
            self.assertTrue(library._journal_matches(journal))


class AgentOutageTests(unittest.TestCase):
    def test_a_codex_error_is_not_a_lemma_attempt_and_goes_back_in_the_queue(self):
        from forge import portfolio
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        with mock.patch.object(portfolio, 'STATE_DIR', root / 'pf'), mock.patch('forge.scheduler.RUNS', root / 'runs'), \
             mock.patch('forge.scheduler.DATA', root), mock.patch.object(portfolio.bench, 'load', return_value=[dict(name='p', statement=': True')]):
            runner = portfolio.Portfolio('t-out', workers=1, max_tasks=1000, dry_run=True)
            runner.items = {'p': dict(name='p', statement=': True')}
            runner.state = dict(run='t-out', problems={'p': dict(set='s', solved_by=None, dags={'d1': dict(skeleton='', holes=[dict(lemma='L', args=[])], status='open')})},
                                lemmas={'L': dict(set='s', problem='p', statement='True', hash='h', status='open', dags=['d1'], attempts=1)})
            runner.file_lock, runner.lemma_seconds, runner.scratch, runner.lemma_attempts = threading.Lock(), 60, root / 'scratch', 2
            runner.queue, runner.split, runner.depth = [], 0, 1
            (root / 'scratch' / 'a1').mkdir(parents=True)
            with mock.patch.object(runner, '_invoke', return_value=(1, '', None, False)):
                runner._lemma('a1', 'p', 'L')
        self.assertEqual(runner.state['lemmas']['L']['attempts'], 1)  # 没有多算一次
        self.assertEqual(runner.state['lemmas']['L']['status'], 'open')
        self.assertEqual(runner.queue, [('lemma', 'p', 'L')])
        self.assertEqual(runner.records[-1]['outcome'], 'agent_error')

    def test_scheduler_pauses_after_consecutive_agent_errors_even_with_a_high_failure_limit(self):
        from forge import scheduler
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        with mock.patch.object(scheduler, 'RUNS', Path(tmp.name)):
            runner = scheduler.Scheduler('t-err', workers=1, max_tasks=10, dry_run=True, max_failures=1000,
                                         agent_error_limit=3, cooldowns=1)
            runner.log = Path(tmp.name) / 't-err.jsonl'
            for _ in range(3):
                runner._record(dict(mode='x', outcome='agent_error', progress=False, exit=1, tokens=0))
            self.assertGreater(runner.paused_until, 0)
            self.assertIsNone(runner.stop_reason)
            runner.paused_until = 0
            runner._record(dict(mode='x', outcome='unsolved', progress=False, exit=0, tokens=500))  # 一次正常的失败清零
            for _ in range(3):
                runner._record(dict(mode='x', outcome='agent_error', progress=False, exit=1, tokens=0))
            self.assertIn('没有跑起来', runner.stop_reason)  # 冷却用完就停下，不再空转
