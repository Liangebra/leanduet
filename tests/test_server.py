import json
import threading
import unittest
from http.server import ThreadingHTTPServer
import urllib.error
import urllib.request
from unittest.mock import patch
from types import SimpleNamespace
from server import check_source, ai_request, Handler, MAX_TRACE_SOURCE
class CheckerTests(unittest.TestCase):
    def test_rejects_incomplete_proof(self):
        self.assertEqual(check_source('theorem t : True := by sorry')['status'],'rejected')
    @patch('server.shutil.which',return_value=None)
    def test_unavailable(self,_):
        self.assertEqual(check_source('theorem t : True := by trivial')['status'],'unavailable')
    @patch('server.shutil.which',return_value='/usr/bin/lean')
    @patch('server.subprocess.run',return_value=SimpleNamespace(returncode=1,stdout='',stderr='error'))
    def test_error(self,*_):
        self.assertEqual(check_source('bad')['status'],'failed')
    @patch('server.shutil.which',return_value='/usr/bin/lean')
    @patch('server.subprocess.run',return_value=SimpleNamespace(returncode=0,stdout='warning: declaration uses sorry',stderr=''))
    def test_warning(self,*_):
        self.assertEqual(check_source('theorem t : True := by trivial')['status'],'failed')
    @patch('server.shutil.which',return_value='/usr/bin/lean')
    @patch('server.subprocess.run',return_value=SimpleNamespace(returncode=0,stdout='',stderr=''))
    def test_pass(self,*_):
        self.assertEqual(check_source('theorem t : True := by trivial')['status'],'passed')
    @patch.dict('os.environ',{},clear=True)
    def test_ai_disabled(self):
        with self.assertRaises(ValueError): ai_request('x','y','explain')


class TraceApiTests(unittest.TestCase):
    def post(self, source):
        payload=json.dumps({'source':source},ensure_ascii=False).encode('utf-8')
        with patch.object(Handler,'project',None):
            with ThreadingHTTPServer(('127.0.0.1',0),Handler) as httpd:
                thread=threading.Thread(target=httpd.serve_forever,daemon=True)
                thread.start()
                try:
                    host=f'127.0.0.1:{httpd.server_port}'
                    request=urllib.request.Request(
                        f'http://{host}/api/trace',
                        data=payload,
                        headers={
                            'Content-Type':'application/json',
                            'Origin':f'http://{host}',
                        },
                        method='POST',
                    )
                    try:
                        response=urllib.request.urlopen(request,timeout=5)
                    except urllib.error.HTTPError as error:
                        response=error
                    with response:
                        return response.code,json.loads(response.read().decode('utf-8'))
                finally:
                    httpd.shutdown()
                    thread.join(timeout=5)

    @patch('server.semantic.trace')
    def test_trace_route_returns_real_adapter_schema(self, trace):
        source='theorem t : True := by trivial -- λ'
        expected={'schema':1,'tactics':[{'syntax':'trivial'}]}
        trace.return_value=expected
        status,body=self.post(source)
        self.assertEqual(status,200)
        self.assertEqual(body,expected)
        trace.assert_called_once_with(source,None)

    @patch('server.semantic.trace')
    def test_trace_route_bounds_utf8_source_bytes(self, trace):
        source='界'*(MAX_TRACE_SOURCE//3+1)
        self.assertLessEqual(len(source),MAX_TRACE_SOURCE)
        self.assertGreater(len(source.encode('utf-8')),MAX_TRACE_SOURCE)
        status,body=self.post(source)
        self.assertEqual(status,400)
        self.assertIn('12 KiB',body['error'])
        trace.assert_not_called()
