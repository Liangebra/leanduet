"""LeanDuet local-only server. Trusted code only; NOT a sandbox."""
import argparse
import http.server
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import urllib.request
import urllib.error
import semantic

ROOT = Path(__file__).resolve().parent
MAX_BODY = 128 * 1024

def check_source(source, project=None):
    if re.search(r'\b(?:sorry|admit|sorryAx)\b', source):
        return {'status':'rejected','output':'Explicit sorry/admit/sorryAx is not allowed.'}
    command = ['lake','env','lean'] if project else ['lean']
    if not shutil.which(command[0]):
        return {'status':'unavailable','output':f'{command[0]} not found. Install Lean via elan.'}
    try:
        with tempfile.TemporaryDirectory(prefix='leanduet-') as folder:
            path = Path(folder)/'Proof.lean'
            path.write_text(source, encoding='utf-8')
            result = subprocess.run(command+[str(path)],cwd=project or ROOT,capture_output=True,text=True,encoding='utf-8',errors='replace',timeout=30,check=False)
            output = result.stdout + result.stderr
            incomplete = bool(re.search(r'\bsorry\b',output,re.I))
            return {'status':'passed' if result.returncode==0 and not incomplete else 'failed','output':output[-20000:] or '(no diagnostics)'}
    except subprocess.TimeoutExpired:
        return {'status':'timeout','output':'Lean exceeded 30 seconds.'}
    except OSError as exc:
        return {'status':'unavailable','output':str(exc)}

def ai_request(source, prose, mode):
    endpoint,model = os.getenv('LEANDUET_AI_URL'),os.getenv('LEANDUET_AI_MODEL')
    if not endpoint or not model:
        raise ValueError('AI is disabled. Set LEANDUET_AI_URL and LEANDUET_AI_MODEL.')
    system = ('Return only Lean 4 source, no Markdown. Preserve exact imports and complete theorem header. Use space-indented proof lines; no sorry/admit.' if mode=='propose' else 'Explain the supplied Lean proof as a mathematical narrative, distinguishing actual reasoning from opaque tactics and referenced lemmas. Do not invent omitted arguments. Use LaTeX notation where helpful.')
    payload={'model':model,'messages':[{'role':'system','content':system},{'role':'user','content':json.dumps({'source':source,'requested_proof':prose},ensure_ascii=False)}]}
    headers={'Content-Type':'application/json'}
    if os.getenv('LEANDUET_AI_KEY'):
        headers['Authorization']='Bearer '+os.environ['LEANDUET_AI_KEY']
    req=urllib.request.Request(endpoint,data=json.dumps(payload).encode(),headers=headers)
    with urllib.request.urlopen(req,timeout=60) as response:
        result=json.loads(response.read(512*1024))
    value=result['choices'][0]['message']['content'].strip()
    if not value or len(value.encode())>MAX_BODY: raise ValueError('Empty or oversized response.')
    return {'source':value+'\n'} if mode=='propose' else {'narrative':value}

class Handler(http.server.SimpleHTTPRequestHandler):
    project=None
    def __init__(self,*args,**kwargs):
        super().__init__(*args,directory=str(ROOT/'web'),**kwargs)
    def allowed(self):
        port=self.server.server_port
        host=self.headers.get('Host','')
        return host in {f'127.0.0.1:{port}',f'localhost:{port}'} and self.headers.get('Origin','') in {'',f'http://{host}'}
    def do_GET(self):
        if not self.allowed(): return self.send_error(403)
        super().do_GET()
    def do_HEAD(self):
        if not self.allowed(): return self.send_error(403)
        super().do_HEAD()
    def send_json(self,status,data):
        body=json.dumps(data,ensure_ascii=False).encode()
        self.send_response(status)
        self.send_header('Content-Type','application/json; charset=utf-8')
        self.send_header('Cache-Control','no-store')
        self.send_header('Content-Length',str(len(body)))
        self.end_headers()
        self.wfile.write(body)
    def do_POST(self):
        if not self.allowed(): return self.send_json(403,{'error':'Local same-origin requests only.'})
        if self.headers.get_content_type()!='application/json': return self.send_json(415,{'error':'Expected JSON.'})
        try:
            n=int(self.headers.get('Content-Length','0'))
            if not 0<n<=MAX_BODY: raise ValueError('Invalid request size.')
            data=json.loads(self.rfile.read(n))
            source=data.get('source')
            if not isinstance(source,str) or not source.strip(): raise ValueError('Source must be nonempty text.')
            if self.path=='/api/check': return self.send_json(200,check_source(source,self.project))
            if self.path=='/api/structure': return self.send_json(200,semantic.extract(source,self.project))
            if self.path=='/api/search': return self.send_json(200,semantic.search(source,data.get('path'),data.get('rule',''),self.project))
            if self.path=='/api/patch': return self.send_json(200,semantic.patch(source,data.get('path'),data.get('replacement'),self.project))
            if self.path=='/api/informath': return self.send_json(200,semantic.informath(source,self.project))
            if self.path in {'/api/propose','/api/explain'}:
                prose=data.get('prose','')
                if not isinstance(prose,str): raise ValueError('Prose must be text.')
                return self.send_json(200,ai_request(source,prose,self.path[5:]))
            return self.send_json(404,{'error':'Unknown endpoint.'})
        except (ValueError,TypeError,AttributeError,KeyError,IndexError) as exc:
            return self.send_json(400,{'error':str(exc)})
        except subprocess.TimeoutExpired:
            return self.send_json(504,{'error':'Semantic tool timed out.'})
        except OSError as exc:
            return self.send_json(502,{'error':f'Local service or AI endpoint failed: {type(exc).__name__}'})

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--port',type=int,default=8765)
    parser.add_argument('--project',type=Path)
    args=parser.parse_args()
    if args.project and not args.project.is_dir(): parser.error('--project must be a directory')
    Handler.project=args.project.resolve() if args.project else None
    with http.server.ThreadingHTTPServer(('127.0.0.1',args.port),Handler) as server:
        print(f'LeanDuet: http://127.0.0.1:{server.server_port}',flush=True)
        server.serve_forever()
if __name__=='__main__': main()
