import unittest
from unittest.mock import patch
from types import SimpleNamespace
import semantic

class SemanticTests(unittest.TestCase):
    def test_name(self):
        self.assertEqual(semantic._name("theorem t : True := by\n  trivial"), "t")
    def test_multiple(self):
        with self.assertRaises(ValueError):
            semantic._name("theorem t : True := by\n  trivial\ntheorem u : True := by\n  trivial")
    def test_sorry(self):
        with self.assertRaises(ValueError):
            semantic.extract("theorem t : True := by\n  sorry")
    @patch("semantic.shutil.which", return_value="/usr/bin/lean")
    @patch("semantic.subprocess.run", return_value=SimpleNamespace(returncode=0,stdout='info: LEANDUET_JSON:{"schema":1,"tree":{"kind":"hypothesis"}}\n',stderr=""))
    def test_extract(self,*_):
        self.assertEqual(semantic.extract("theorem t : True := by\n  trivial")["tree"]["kind"],"hypothesis")
    @patch.dict("os.environ",{},clear=True)
    def test_informath_disabled(self):
        with self.assertRaises(ValueError):
            semantic.informath("theorem t : True := by\n  trivial")
