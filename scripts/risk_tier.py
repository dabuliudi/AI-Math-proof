"""Classify a change into a review risk tier: low, medium or high.

The tier of a change is the highest tier of any path it touches. The rules live in
RULES below and are described for people in docs/DEVELOPMENT.md.

    python scripts/risk_tier.py                  # diff of HEAD against origin/main
    python scripts/risk_tier.py --base <ref>     # diff of HEAD against <ref>
    python scripts/risk_tier.py path ...         # classify the given paths
    python scripts/risk_tier.py --json ...       # machine-readable output
"""
import argparse
import fnmatch
import json
import subprocess
import sys

ORDER = {'low': 0, 'medium': 1, 'high': 2}

# First match wins. A path that matches nothing is medium.
RULES = [
    # high: code and data that decide whether something counts as proved, solved or improved,
    # the Lean toolchain those decisions run on, and the review process itself.
    ('high', 'forge/verify.py'),
    ('high', 'forge/statement.py'),
    ('high', 'forge/audit.py'),
    ('high', 'forge/leanrun.py'),
    ('high', 'forge/library.py'),
    ('high', 'forge/bench.py'),
    ('high', 'forge/improve.py'),
    ('high', 'forge/regressions.py'),
    ('high', 'forge/portfolio.py'),
    ('low', 'forge/data/bench/runs/*'),
    ('high', 'forge/data/bench/*.jsonl'),
    ('high', 'forge/data/regressions.jsonl'),
    ('high', 'lean/Forge.lean'),
    ('high', 'lean/Forge/*'),
    ('high', 'lean/lakefile.*'),
    ('high', 'lean/lean-toolchain'),
    ('high', 'lean/lake-manifest.json'),
    ('high', '.github/*'),
    ('high', 'scripts/risk_tier.py'),
    ('high', 'docs/DEVELOPMENT.md'),
    ('high', 'CLAUDE.md'),
    ('high', 'AGENTS.md'),
    # low: machine-written library and run output (CI replays the library), and prose.
    ('low', 'lean/Mathlib2.lean'),
    ('low', 'lean/Mathlib2/*'),
    ('low', 'lean/Research/*'),
    ('low', 'forge/data/*'),
    ('low', 'phase2/benchmarks/*'),
    ('low', 'reports/*'),
    ('low', 'audits/*'),
    ('low', '*.md'),
]


def tier_of(path):
    for tier, pattern in RULES:
        if fnmatch.fnmatchcase(path, pattern):
            return tier
    return 'medium'


def classify(paths):
    tiers = {path: tier_of(path) for path in paths}
    overall = max(tiers.values(), key=ORDER.__getitem__, default='low')
    return overall, tiers


def changed_paths(base):
    merge_base = subprocess.run(['git', 'merge-base', base, 'HEAD'], capture_output=True, text=True, check=True).stdout.strip()
    out = subprocess.run(['git', 'diff', '--name-only', merge_base, 'HEAD'], capture_output=True, text=True, check=True).stdout
    return [line for line in out.splitlines() if line]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('paths', nargs='*')
    parser.add_argument('--base', default='origin/main')
    parser.add_argument('--json', action='store_true')
    args = parser.parse_args(argv)
    paths = args.paths or changed_paths(args.base)
    overall, tiers = classify(paths)
    if args.json:
        print(json.dumps(dict(tier=overall, paths=tiers), ensure_ascii=False, indent=2))
    else:
        print(overall)
        for path, tier in sorted(tiers.items(), key=lambda item: (-ORDER[item[1]], item[0])):
            if tier != 'low' or overall == 'low':
                print(f'  {tier:6} {path}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
