import io
import unittest
from lean_lsp import read_message,write_message,complete
class LspProtocolTest(unittest.TestCase):
    def test_unicode_framing(self):
        s=io.BytesIO()
        write_message(s,{"id":1,"result":"∀ α"})
        s.seek(0)
        self.assertEqual(read_message(s)["result"],"∀ α")
    def test_invalid_position(self):
        with self.assertRaises(ValueError): complete("a",0,2)
