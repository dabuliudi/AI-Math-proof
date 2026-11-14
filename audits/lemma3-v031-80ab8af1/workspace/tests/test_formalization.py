import os
import re
import unittest
import subprocess
import tempfile
from pathlib import Path
from unittest.mock import patch
from mathlib2.formalization import templates, check_template


class FormalizationTests(unittest.TestCase):
    def test_template_provenance_and_scope(self):
        t=templates()['mason_lemma1']
        self.assertEqual(t['scope'],'target')
        self.assertEqual(t['provenance']['category'],'Theorem Reuse')
        self.assertFalse(t['provenance']['new_proof'])
        self.assertNotRegex(t['source'],r'\b(sorry|admit|axiom)\b')
        self.assertRegex('Lemma 1.For a nonzero polynomiala∈k[t],a/rad(a)dividesa ′.',t['source_match'])
        self.assertIsNone(re.search(t['source_match'],'Lemma 2.For any nonzero a, something else'))

    def test_untrusted_template_rejected(self):
        with self.assertRaises(ValueError):
            check_template('by sorry')
        with self.assertRaises(ValueError):
            check_template('mason_lemma1',timeout=1000)

    def test_version_timeout_does_not_claim_proof_compilation(self):
        # 模拟基础设施故障，不作为真实论文证明证据；日志写入临时目录。
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            (root/'lean-toolchain').write_text('leanprover/lean4:v4.24.0',encoding='utf-8')
            with patch('mathlib2.formalization.ROOT',root), patch('mathlib2.formalization.PROJECT',root), \
                 patch.dict(os.environ,{'MATHLIB2_LAKE':'test-lake'}), \
                 patch('mathlib2.formalization.subprocess.run',side_effect=subprocess.TimeoutExpired('version',60)) as version, \
                 patch('mathlib2.formalization.subprocess.Popen') as compiler:
                result=check_template('mason_lemma3')
            self.assertFalse(result['accepted'])
            self.assertEqual(result['timeout_phase'],'toolchain_version')
            self.assertEqual(result['status'],'timeout')
            self.assertIn('尚未开始证明编译',result['reason'])
            self.assertEqual(version.call_args.kwargs['timeout'],60)
            compiler.assert_not_called()

    @unittest.skipUnless(os.environ.get('MATHLIB2_INTEGRATION')=='1','需要真实 Lean 工具链及多项式模块缓存')
    def test_real_lemma1(self):
        result=check_template('mason_lemma1')
        self.assertTrue(result['accepted'],result)
        self.assertEqual(result['returncode'],0)
        self.assertEqual(result['status'],'verified')
        self.assertTrue(result['lean_version'])
        self.assertLessEqual(set(result['axioms']),{'propext','Classical.choice','Quot.sound'})
