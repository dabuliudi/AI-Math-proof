import argparse
import json
from .gateway import run_from_env

SMOKE_GOAL='对任意自然数 a、b、c，若 a ≤ b 且 b ≤ c，则 a ≤ c。请提出证明计划。'


def main():
    parser=argparse.ArgumentParser(description='独立数学规划API Gateway；不会执行Lean或Tool Calling')
    parser.add_argument('--goal',default=SMOKE_GOAL,help='仅发送此数学目标，不读取数据库或旧证明')
    args=parser.parse_args()
    result=run_from_env(args.goal)
    print(json.dumps(result,ensure_ascii=False,indent=2))
    return 0 if result['status']=='plan_generated' else 2


if __name__=='__main__': raise SystemExit(main())
