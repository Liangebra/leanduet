import unittest
from unittest.mock import patch
from types import SimpleNamespace
from server import check_source, ai_request
class CheckerTests(unittest.TestCase):
    def test_placeholder(self):
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
