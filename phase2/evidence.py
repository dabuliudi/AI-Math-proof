import hashlib
import json
import time
from datetime import datetime,timezone
from pathlib import Path


def digest(text):
    return hashlib.sha256(text.encode('utf-8')).hexdigest()


class Journal:
    def __init__(self,folder):
        self.folder=Path(folder)
        self.folder.mkdir(parents=True,exist_ok=False)
        self.sequence=0
        self.previous=''

    def save(self,name,value):
        (self.folder/name).write_text(json.dumps(value,ensure_ascii=False,indent=2),encoding='utf-8')

    def event(self,kind,**payload):
        self.sequence+=1
        record=dict(sequence=self.sequence,time=datetime.now(timezone.utc).isoformat(),monotonic=time.monotonic(),
                    kind=kind,payload=payload,previous_hash=self.previous)
        record['hash']=digest(json.dumps(record,ensure_ascii=False,sort_keys=True))
        self.previous=record['hash']
        with (self.folder/'events.jsonl').open('a',encoding='utf-8') as stream:
            stream.write(json.dumps(record,ensure_ascii=False)+'\n')
        return record['sequence']


class DynamicDAG:
    def __init__(self,journal):
        self.journal=journal
        self.nodes={}
        self.edges=[]

    def add(self,key,statement,parents=(),origin='Rule Engine',status='planned',**metadata):
        if key in self.nodes or any(p not in self.nodes for p in parents):
            raise ValueError('重复节点或未建立的前提')
        self.nodes[key]=dict(id=key,statement=statement,status=status,origin=origin,**metadata)
        for parent in parents:
            self.edges.append(dict(source=parent,target=key,type='proof_dependency',evidence=metadata.get('rule','context/conjunction')))
        self.nodes[key]['planned_event']=self.journal.event('dag_node_planned',node=self.nodes[key].copy(),parents=list(parents))

    def update(self,key,status,**metadata):
        self.nodes[key].update(status=status,**metadata)
        self.journal.event('dag_node_updated',node=key,status=status,**metadata)

    def snapshot(self):
        depths={}
        for key in self.nodes:
            parents=[e['source'] for e in self.edges if e['target']==key]
            if any(p not in depths for p in parents):
                raise ValueError('非拓扑DAG')
            depths[key]=max([depths[p]+1 for p in parents]+[0])
        return dict(nodes=list(self.nodes.values()),edges=self.edges,depth=max(depths.values(),default=0),depths=depths)
