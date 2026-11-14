import argparse
import json
from .pipeline import run
from .store import Store


def main():
    parser = argparse.ArgumentParser(description='Mathlib2 本地演示')
    parser.add_argument('--db', default='data/mathlib2.sqlite')
    sub = parser.add_subparsers(dest='cmd', required=True)
    demo = sub.add_parser('demo', help='导入并运行受预算限制的探索')
    demo.add_argument('file', nargs='?', default='samples/nat.md')
    demo.add_argument('--limit', type=int, default=4)
    sub.add_parser('inspect', help='查看持久化记录')
    approve = sub.add_parser('approve', help='人工审核进入已验证库')
    approve.add_argument('id', type=int)
    approve.add_argument('--reviewer', required=True)
    approve.add_argument('--note', required=True)
    args = parser.parse_args()
    store = Store(args.db)
    if args.cmd == 'demo':
        result = run(store, args.file, args.limit)
    elif args.cmd == 'approve':
        store.approve(args.id, args.reviewer, args.note)
        result = {'approved': args.id}
    else:
        result = {t: store.rows(t) for t in ('sources', 'candidates', 'events', 'verified')}
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
