"""One-shot Lean language-server completion for trusted local documents."""
import json
import os
from pathlib import Path
import queue
import shutil
import signal
import subprocess
import tempfile
import threading
import time

ROOT=Path(__file__).resolve().parent
MAX_MESSAGE=16*1024*1024

def read_message(stream):
    headers={}
    while True:
        line=stream.readline(4096)
        if not line:
            raise EOFError("Lean language server closed its stream.")
        if line in (b"\r\n",b"\n"):
            break
        key,sep,value=line.decode("ascii").partition(":")
        if not sep:
            raise ValueError("Invalid LSP header.")
        headers[key.lower()]=value.strip()
    size=int(headers["content-length"])
    if not 0<size<=MAX_MESSAGE:
        raise ValueError("Oversized LSP message.")
    data=stream.read(size)
    if len(data)!=size:
        raise EOFError("Incomplete LSP message.")
    return json.loads(data)

def write_message(stream,message):
    data=json.dumps({"jsonrpc":"2.0",**message},ensure_ascii=False).encode("utf-8")
    stream.write(f"Content-Length: {len(data)}\r\n\r\n".encode("ascii")+data)
    stream.flush()

def complete(source,line,character,project=None):
    if type(line) is not int or type(character) is not int or line<0 or character<0:
        raise ValueError("Expected a nonnegative UTF-16 LSP position.")
    lines=source.split("\n")
    if line>=len(lines) or character>len(lines[line].encode("utf-16-le"))//2:
        raise ValueError("Completion position is outside the document.")
    command=["lake","env","lean","--server"] if project else ["lean","--server"]
    if not shutil.which(command[0]):
        raise ValueError("Lean toolchain not available.")
    cwd=Path(project or ROOT).resolve()
    with tempfile.TemporaryDirectory(prefix="leanduet-lsp-") as d:
        file=Path(d)/"Completion.lean"
        file.write_text(source,encoding="utf-8")
        uri=file.as_uri()
        proc=subprocess.Popen(command,cwd=cwd,stdin=subprocess.PIPE,stdout=subprocess.PIPE,
                              stderr=subprocess.DEVNULL,start_new_session=(os.name=="posix"))
        inbox=queue.Queue(maxsize=256)
        def reader():
            try:
                while True:
                    inbox.put(read_message(proc.stdout))
            except Exception as e:
                try: inbox.put(e,timeout=0.1)
                except queue.Full: pass
        threading.Thread(target=reader,daemon=True).start()
        deadline=time.monotonic()+40
        def send(message): write_message(proc.stdin,message)
        def response(identifier):
            while True:
                try: m=inbox.get(timeout=max(0,deadline-time.monotonic()))
                except queue.Empty: raise ValueError("Lean completion timed out.")
                if isinstance(m,Exception): raise ValueError(str(m))
                if "method" in m and "id" in m:
                    # Never run commands requested by a server; answer standard
                    # configuration queries with empty settings.
                    result=[None]*len(m.get("params",{}).get("items",[])) if m["method"]=="workspace/configuration" else None
                    send({"id":m["id"],"result":result})
                elif m.get("id")==identifier:
                    if m.get("error"): raise ValueError(str(m["error"].get("message","Lean LSP error")))
                    return m.get("result")
        try:
            send({"id":1,"method":"initialize","params":{"processId":os.getpid(),"rootUri":cwd.as_uri(),
                 "capabilities":{"general":{"positionEncodings":["utf-16"]},"textDocument":{"completion":{"completionItem":{"snippetSupport":False,"insertReplaceSupport":True}}}}}})
            response(1)
            send({"method":"initialized","params":{}})
            send({"method":"textDocument/didOpen","params":{"textDocument":{"uri":uri,"languageId":"lean4","version":1,"text":source}}})
            # Lean's test synchronization request waits for elaboration of this
            # document version before querying the native completion handler.
            send({"id":2,"method":"textDocument/waitForDiagnostics","params":{"uri":uri,"version":1}})
            response(2)
            send({"id":3,"method":"textDocument/completion","params":{"textDocument":{"uri":uri},"position":{"line":line,"character":character}}})
            result=response(3)
            items=result.get("items",[]) if isinstance(result,dict) else result or []
            return {"items":items[:40],"isIncomplete":bool(isinstance(result,dict) and result.get("isIncomplete")) or len(items)>40,
                    "provider":"Lean LSP"}
        finally:
            # Lean's server can spawn file workers; kill the whole temporary
            # process group on POSIX, not just the JSON-RPC parent.
            try:
                if os.name=="posix": os.killpg(proc.pid,signal.SIGTERM)
                else: proc.terminate()
            except ProcessLookupError: pass
            try: proc.wait(timeout=2)
            except subprocess.TimeoutExpired:
                if os.name=="posix":
                    try: os.killpg(proc.pid,signal.SIGKILL)
                    except ProcessLookupError: pass
                else: proc.kill()
                proc.wait()
            proc.stdin.close()
            proc.stdout.close()
