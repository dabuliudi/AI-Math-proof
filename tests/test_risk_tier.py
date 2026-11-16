import importlib.util
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


if __name__ == '__main__':
    unittest.main()
