import argparse
import json
from pathlib import Path
from .engine import discover


def main():
    parser=argparse.ArgumentParser(description='Phase 2: no-AI bounded proof discovery')
    parser.add_argument('problem',type=Path)
    parser.add_argument('--budget',type=int,default=12)
    args=parser.parse_args()
    print(json.dumps(discover(json.loads(args.problem.read_text(encoding='utf-8')),budget=args.budget),ensure_ascii=False,indent=2))


if __name__=='__main__': main()
