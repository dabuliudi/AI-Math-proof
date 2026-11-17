import importlib.util
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

spec = importlib.util.spec_from_file_location('risk_tier', Path(__file__).resolve().parents[1] / 'scripts' / 'risk_tier.py')
risk_tier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(risk_tier)


class RiskTierTests(unittest.TestCase):
    def test_paths(self):
        cases = {
            'forge/verify.py': 'high',
            'forge/data/bench/fc_pilot.jsonl': 'high',
            'forge/data/bench/runs/fc-calib-0/results.jsonl': 'low',
            'lean/lakefile.toml': 'high',
            '.github/workflows/ci.yml': 'high',
            'docs/DEVELOPMENT.md': 'high',
            'forge/scheduler.py': 'medium',
            'forge/data/improve/prompts/p.md': 'low',
            'lean/Mathlib2/Shard/S0059.lean': 'low',
            'forge/data/ledger.jsonl': 'low',
            'ROADMAP.md': 'low',
            'app.py': 'medium',
        }
        for path, tier in cases.items():
            self.assertEqual(risk_tier.tier_of(path), tier, path)

    def test_change_takes_highest_tier(self):
        self.assertEqual(risk_tier.classify(['ROADMAP.md', 'forge/scheduler.py'])[0], 'medium')
        self.assertEqual(risk_tier.classify(['forge/data/ledger.jsonl', 'forge/library.py'])[0], 'high')
        self.assertEqual(risk_tier.classify([])[0], 'low')

    def test_head_is_read_as_data_and_renames_count_both_sides(self):
        with tempfile.TemporaryDirectory() as repo:
            def git(*args):
                return subprocess.run(['git', '-C', repo, '-c', 'user.name=t', '-c', 'user.email=t@t', *args],
                                      capture_output=True, text=True, check=True).stdout.strip()
            git('init', '-q')
            Path(repo, 'forge').mkdir()
            Path(repo, 'forge', 'verify.py').write_text('x = 1\n')
            git('add', '-A')
            git('commit', '-qm', 'base')
            base = git('rev-parse', 'HEAD')
            git('mv', 'forge/verify.py', 'forge/moved.py')
            git('commit', '-qm', 'move')
            head = git('rev-parse', 'HEAD')
            git('checkout', '-q', '--detach', base)
            cwd = Path.cwd()
            try:
                os.chdir(repo)
                paths = risk_tier.changed_paths(base, head)
            finally:
                os.chdir(cwd)
            self.assertEqual(sorted(paths), ['forge/moved.py', 'forge/verify.py'])
            self.assertEqual(risk_tier.classify(paths)[0], 'high')


if __name__ == '__main__':
    unittest.main()
