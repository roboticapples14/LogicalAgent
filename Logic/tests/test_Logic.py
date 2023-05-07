import unittest
from .. import Prop
from .. import Literal

class MyTestCase(unittest.TestCase):
    def test_literal(self):
        p = Prop({"p": True, "q": False, "c": True})
        lit = Literal("p", negFlag=False)
        self.assertEqual(lit.evaluate(), True)