import json
import sqlite3
from datetime import datetime, timezone
from pathlib import Path
from .structures import VERSION


class Store:
    def __init__(self, path='data/mathlib2.sqlite'):
        Path(path).parent.mkdir(parents=True, exist_ok=True)
        self.db = sqlite3.connect(path)
        self.db.row_factory = sqlite3.Row
        # 增量迁移前在线备份：保留原始数据库，可关闭应用后恢复。
        if str(path) != ':memory:' and self.db.execute("SELECT name FROM sqlite_master WHERE name='sources'").fetchone() and not self.db.execute("SELECT name FROM sqlite_master WHERE name='workbench_state'").fetchone():
            backup=Path(str(path)+'.before-v03.bak')
            if not backup.exists():
                with sqlite3.connect(backup) as target:
                    self.db.backup(target)
                target.close()
        self.db.executescript('''
        CREATE TABLE IF NOT EXISTS sources(id INTEGER PRIMARY KEY, payload TEXT NOT NULL);
        CREATE TABLE IF NOT EXISTS candidates(id INTEGER PRIMARY KEY, source_id INTEGER, payload TEXT NOT NULL, status TEXT NOT NULL DEFAULT 'unknown');
        CREATE TABLE IF NOT EXISTS events(id INTEGER PRIMARY KEY, candidate_id INTEGER, role TEXT, payload TEXT, created TEXT);
        CREATE TABLE IF NOT EXISTS verified(candidate_id INTEGER PRIMARY KEY, reviewer TEXT NOT NULL, note TEXT NOT NULL, created TEXT NOT NULL);
        CREATE TABLE IF NOT EXISTS document_parses(source_id INTEGER NOT NULL, version TEXT NOT NULL, payload TEXT NOT NULL, PRIMARY KEY(source_id,version));
        CREATE TABLE IF NOT EXISTS math_objects(id INTEGER PRIMARY KEY, source_id INTEGER NOT NULL, object_key TEXT NOT NULL UNIQUE, payload TEXT NOT NULL);
        CREATE TABLE IF NOT EXISTS workbench_state(candidate_id INTEGER PRIMARY KEY, payload TEXT NOT NULL);
        CREATE TABLE IF NOT EXISTS workbench_history(id INTEGER PRIMARY KEY, candidate_id INTEGER NOT NULL, action TEXT NOT NULL, payload TEXT NOT NULL, created TEXT NOT NULL);
        CREATE TABLE IF NOT EXISTS proof_runs(id INTEGER PRIMARY KEY, candidate_id INTEGER NOT NULL, payload TEXT NOT NULL, created TEXT NOT NULL);
        ''')
        columns = {r[1] for r in self.db.execute('PRAGMA table_info(candidates)')}
        if 'dedup_key' not in columns:
            self.db.execute('ALTER TABLE candidates ADD COLUMN dedup_key TEXT')
        self.db.execute('CREATE UNIQUE INDEX IF NOT EXISTS candidate_dedup ON candidates(dedup_key)')
        self.db.commit()

    def add(self, table, payload, source_id=None, dedup_key=None):
        if table == 'sources':
            cur = self.db.execute('INSERT INTO sources(payload) VALUES (?)', (json.dumps(payload, ensure_ascii=False),))
        elif table == 'candidates':
            if dedup_key:
                existing = self.db.execute('SELECT id FROM candidates WHERE dedup_key=?', (dedup_key,)).fetchone()
                if existing:
                    return existing[0]
            cur = self.db.execute('INSERT INTO candidates(source_id,payload,dedup_key) VALUES (?,?,?)', (source_id, json.dumps(payload, ensure_ascii=False), dedup_key))
        else:
            raise ValueError(table)
        self.db.commit()
        return cur.lastrowid

    def event(self, cid, role, payload):
        self.db.execute('INSERT INTO events(candidate_id,role,payload,created) VALUES (?,?,?,?)',
                        (cid, role, json.dumps(payload, ensure_ascii=False), datetime.now(timezone.utc).isoformat()))
        self.db.commit()

    def rows(self, table):
        if table not in {'sources', 'candidates', 'events', 'verified', 'document_parses', 'math_objects','workbench_state','workbench_history','proof_runs'}:
            raise ValueError(table)
        rows = [dict(r) for r in self.db.execute('SELECT * FROM ' + table + ' ORDER BY 1')]
        for row in rows:
            if 'payload' in row:
                row['payload'] = json.loads(row['payload'])
        return rows

    def source_by_hash(self, digest):
        # 兼容 v0.1 JSON 来源，复用最早记录，保留已有重复行。
        return next((r for r in self.rows('sources') if r['payload'].get('sha256') == digest), None)

    def document(self, sid, version=VERSION):
        row = self.db.execute('SELECT payload FROM document_parses WHERE source_id=? AND version=?', (sid,version)).fetchone()
        return json.loads(row[0]) if row else None

    def save_document(self, sid, source):
        with self.db:
            self.db.execute('INSERT OR REPLACE INTO document_parses VALUES (?,?,?)',
                            (sid, source['parser_version'], json.dumps(source, ensure_ascii=False)))
            for obj in source['objects']:
                self.db.execute('INSERT OR IGNORE INTO math_objects(source_id,object_key,payload) VALUES (?,?,?)',
                                (sid, obj['object_key'], json.dumps(obj, ensure_ascii=False)))

    def finish(self, cid, proof, refutation):
        # 单一状态入口；外部模型的“评价”不能决定证明状态。
        p, r = proof['accepted'], refutation['accepted']
        status = 'unknown' if p == r else ('proved' if p else 'refuted')
        self.event(cid, 'evaluation', {'status': status, 'conflict': p and r,
                   'policy': '只依据真实 Lean 验证；两边均通过则隔离为 unknown'})
        self.db.execute('UPDATE candidates SET status=? WHERE id=?', (status, cid))
        self.db.commit()
        return status

    def approve(self, cid, reviewer, note):
        row = self.db.execute('SELECT status FROM candidates WHERE id=?', (cid,)).fetchone()
        events = [e for e in self.rows('events') if e['candidate_id'] == cid and e['role'] == 'proving']
        if not row or row['status'] != 'proved' or not events or not events[-1]['payload'].get('accepted'):
            raise ValueError('仅 Lean 已证明候选可进入已验证知识库')
        if not reviewer.strip() or not note.strip():
            raise ValueError('请输入审核人及原文与形式化一致性审核意见')
        self.db.execute('INSERT INTO verified VALUES (?,?,?,?)',
                        (cid, reviewer.strip(), note.strip(), datetime.now(timezone.utc).isoformat()))
        self.db.commit()
