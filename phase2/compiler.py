"""只接受内部结构生成的源文件；不运行模型任意Lean代码。"""
import os
import re
import subprocess
import time
from pathlib import Path
from .evidence import digest

ROOT=Path(__file__).resolve().parents[1]
IMPORT='import Mathlib.RingTheory.Polynomial.Radical\n'
ALLOWED={'propext','Classical.choice','Quot.sound'}


class Compiler:
    def __init__(self,journal,timeout=45):
        self.journal=journal
        self.timeout=timeout
        self.lake=ROOT/'.tools/lean-4.24.0-windows/bin/lake.exe'
        self.counter=0
        self.env=os.environ.copy()
        self.env['PATH']=str(self.lake.parent)+os.pathsep+self.env.get('PATH','')

    def execute(self,path,timeout=None):
        command=[str(self.lake),'env','lean','-M','2048',str(Path(path).resolve())]
        start=time.perf_counter()
        try:
            p=subprocess.Popen(command,cwd=ROOT/'lean',env=self.env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,encoding='utf-8',errors='replace')
            try:
                stdout,stderr=p.communicate(timeout=timeout or self.timeout)
                result=dict(returncode=p.returncode,stdout=stdout,stderr=stderr,status='completed')
            except subprocess.TimeoutExpired:
                subprocess.run(['taskkill','/PID',str(p.pid),'/T','/F'],capture_output=True)
                p.kill(); stdout,stderr=p.communicate()
                result=dict(returncode=None,stdout=stdout,stderr=stderr,status='timeout')
        except OSError as exc:
            result=dict(returncode=None,stdout='',stderr=str(exc),status='unavailable')
        result.update(command=command,cwd=str(ROOT/'lean'),elapsed=time.perf_counter()-start)
        return result

    def check(self,source,names,goal):
        self.counter+=1
        stem=f'attempt-{self.counter:03d}'
        path=self.journal.folder/(stem+'.lean')
        path.write_text(source,encoding='utf-8')
        self.journal.event('compile_started',goal=goal,path=str(path),source_sha256=digest(source),declarations=names)
        result=self.execute(path)
        audits={}
        for name in names:
            m=re.search("'"+re.escape(name)+r"' depends on axioms:\s*\[([^\]]*)\]",result['stdout'])
            empty="'"+name+"' does not depend on any axioms" in result['stdout']
            used=[s.strip() for s in m[1].split(',') if s.strip()] if m else []
            audits[name]=dict(axioms=used,accepted=bool(m or empty) and set(used)<=ALLOWED)
        bad=bool(re.search(r'\b(?:sorry|admit|axiom)\b',source) or 'sorryAx' in result['stdout'])
        result.update(accepted=result['returncode']==0 and not bad and bool(audits) and all(x['accepted'] for x in audits.values()),
                      audits=audits,source=source,source_sha256=digest(source),goal=goal,artifact=str(path),log=stem+'.json')
        self.journal.save(stem+'.json',result)
        self.journal.event('compile_finished',goal=goal,log=result['log'],accepted=result['accepted'],status=result['status'])
        return result

    def metadata(self):
        try:
            p=subprocess.run([str(self.lake),'env','lean','--version'],cwd=ROOT/'lean',env=self.env,capture_output=True,text=True,encoding='utf-8',timeout=60)
            version=dict(returncode=p.returncode,stdout=p.stdout,stderr=p.stderr)
        except (OSError,subprocess.TimeoutExpired) as exc:
            version=dict(error=str(exc))
        import json
        return dict(lean=version,toolchain=(ROOT/'lean/lean-toolchain').read_text().strip(),
                    mathlib=json.loads((ROOT/'lean/lake-manifest.json').read_text())['packages'][0])
