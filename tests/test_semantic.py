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

    @patch("semantic._run_lean", return_value={"localType":"R","bindings":[{"name":"x","type":"Nat"},{"name":"hx","type":"P x"}]})
    def test_existential_chain_traces_both_bindings(self, run):
        step={"kind":"obtain","source":"h","copy":"duet_exists_x","name":"x","evidenceName":"hx","type":"Nat","evidenceType":"P x"}
        result=semantic.infer_chain("theorem t : True := by\n  trivial","root",[step,{"kind":"conclude","type":"R","application":"f x hx"}])
        self.assertEqual([b["name"] for b in result["bindings"]],["x","hx"])
        self.assertIn("rcases duet_exists_x with ⟨x, hx⟩",result["term"])
        self.assertIn("change P x at hx",result["term"])
        self.assertIn("duet_trace_object x",run.call_args.args[0])
        self.assertIn("duet_trace hx",run.call_args.args[0])

    def test_existential_chain_rejects_malformed_bindings_before_lean(self):
        step={"kind":"obtain","source":"h","copy":"duet_exists_x","name":"x","evidenceName":"hx","type":"Nat","evidenceType":"P x"}
        for altered in ({"copy":"h"},{"evidenceName":"x"},{"name":"x; sorry"},{"evidenceType":"P x\n  sorry"}):
            with self.subTest(altered=altered), patch("semantic._run_lean") as run:
                with self.assertRaises(ValueError):
                    semantic.infer_chain("theorem t : True := by\n  trivial","root",[{**step,**altered},{"kind":"conclude","application":"hx"}])
                run.assert_not_called()

    @patch("semantic._run_lean",return_value={"localType":"R","bindings":[{"name":"localQ","type":"Q"}]})
    def test_local_lemma_is_compiled_in_a_child_proof_scope(self,run):
        step={"kind":"local-lemma","name":"localQ","type":"Q","subgoals":[
            {"id":"proof","goal":"Q","steps":[{"kind":"conclude","type":"Q","application":"hq"}]}
        ]}
        result=semantic.infer_chain("theorem t : True := by\n  trivial","root",[step,{"kind":"conclude","type":"R","application":"gr localQ"}])
        self.assertIn("have localQ : Q := by\n    show Q\n    exact hq",result["term"])
        self.assertIn("exact gr localQ",result["term"])
        self.assertEqual([binding["name"] for binding in result["bindings"]],["localQ"])
        self.assertIn("duet_trace localQ",run.call_args.args[0])

    def test_local_lemma_interface_rejects_wrong_goal_and_shadowing_before_lean(self):
        valid={"kind":"local-lemma","name":"localQ","type":"Q","subgoals":[
            {"id":"proof","goal":"Q","steps":[{"kind":"conclude","type":"Q","application":"hq"}]}
        ]}
        for altered,sequence in (({"subgoals":[{"id":"proof","goal":"R","steps":[{"kind":"conclude","application":"hq"}]}]},None),
                                 ({"name":"localQ"},[{"kind":"establish","name":"localQ","type":"Q","application":"hq"},valid,{"kind":"conclude","type":"R","application":"gr localQ"}])):
            step={**valid,**altered}
            steps=sequence or [step,{"kind":"conclude","type":"R","application":"gr localQ"}]
            with self.subTest(altered=altered),patch("semantic._run_lean") as run:
                with self.assertRaises(ValueError):
                    semantic.infer_chain("theorem t : True := by\n  trivial","root",steps)
                run.assert_not_called()
