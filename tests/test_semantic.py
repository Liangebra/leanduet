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

    @patch.dict("os.environ",{"LEANDUET_INFORMATH_ROOT":".","LEANDUET_INFORMATH_TOOLCHAIN":"leanprover/lean4:v4.36.0"},clear=True)
    @patch("semantic.shutil.which",return_value="/usr/bin/RunInformath")
    @patch("semantic.subprocess.run",return_value=SimpleNamespace(returncode=0,stdout="Informath output",stderr=""))
    def test_informath_invokes_external_cli(self,run,_):
        r=semantic.informath("theorem t : True := by\n  trivial")
        self.assertEqual(r["provider"],"Informath")
        self.assertFalse(r["verifiedAlignment"])
        self.assertEqual(run.call_args.args[0][1:3],["-from-formalism=lean","-proof-text"])
        self.assertEqual(run.call_args.kwargs["env"]["ELAN_TOOLCHAIN"],"leanprover/lean4:v4.36.0")

    def test_ordered_application(self):
        self.assertTrue(semantic._ordered_application("Exists.intro a (And.intro hm hp)"))
        self.assertTrue(semantic._ordered_application("f (g (h x))"))
        self.assertTrue(semantic._ordered_application("?"))
        for bad in ("f (g x", "f g)", "f (by exact h)", "f sorry", "f (g x); sorry", "f (g x)\\n#check Nat", "f " + "x "*9):
            self.assertFalse(semantic._ordered_application(bad),bad)
