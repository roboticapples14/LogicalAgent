import sys
sys.path.insert(0, '/Users/nvalett/Documents/Natalie/DTU/AI/IntroAI23')
import copy
import unittest
from LogicalAgent.AI.Agent import Agent
import LogicalAgent.AI.rationality_postulates as postulates
import sympy
import sympy.abc as Literal
from itertools import combinations as combinations
from sympy.logic.boolalg import to_cnf

class MyTestCase(unittest.TestCase):

    def get_clause_sets(self):
        formula_str = "(x & y) | (~z)"
        formula = sympy.sympify(formula_str)
        cnf_formula = to_cnf(formula)
        a = Agent(set([]))
        print(a.get_clause_sets(cnf_formula))
        self.assertTrue(True)

    def test_perm(self):
        perm = combinations(set([1,2,3]), 2)
        print(set(perm))

    def test_reduce(self):
        lit_set1 = set([Literal.A, ~Literal.C])
        lit_set2 = set([Literal.A, Literal.C])
        a = Agent(set([]))
        self.assertEqual([Literal.A], a.reduce_operation(lit_set1, lit_set2))

    def test_resolution(self):
        a = Agent(set([Literal.A >> Literal.B, Literal.A]))
        self.assertFalse(a.resolution(~Literal.B))

    def test_entailment(self):
        a = Agent(set())
        self.assertFalse(a.entailment(Literal.P >> Literal.Q, Literal.Q))
        
    def test_entailment2(self):
        a = Agent(set())
        self.assertTrue(a.entailment((Literal.P >> Literal.Q) & Literal.P, Literal.Q))

    def test_intersection(self):
        a1 = Agent(set([Literal.B, Literal.P >> Literal.Q]))
        a2 = Agent(set([Literal.B, Literal.A]))
        self.assertEqual([Literal.B], a1.intersection(a1.belief_base, a2.belief_base))

    def test_revision1(self):
        before = set([Literal.P, Literal.P >> Literal.Q])
        predict = ~Literal.Q
        a = Agent(before)
        a.add_predict(predict)
        revision_correct = a.belief_base == {Literal.P >> Literal.Q, ~Literal.Q} or a.belief_base == {Literal.P, ~Literal.Q}
        self.assertTrue(revision_correct)
        self.assertTrue(postulates.test_all_postulates(before, a.belief_base, predict))

    def test_revision2(self):
        before = set([Literal.P, Literal.P >> Literal.Q])
        predict = Literal.Q
        a = Agent(before)
        a.add_predict(predict)
        self.assertEqual(a.belief_base, set([Literal.P, Literal.P >> Literal.Q, Literal.Q]))
        self.assertTrue(postulates.test_all_postulates(before, a.belief_base, predict))

    def test_revision3(self):
        before = set([Literal.P])
        predict = Literal.P >> Literal.Q
        a = Agent(before)
        a.add_predict(predict)
        self.assertEqual(a.belief_base, set([Literal.P, Literal.P >> Literal.Q]))
        self.assertTrue(postulates.test_all_postulates(before, a.belief_base, predict))

    def test_revision4(self):
        before = set([Literal.A, ~Literal.B])
        predict = Literal.A >> Literal.B
        a = Agent(before)
        a.add_predict(predict)
        self.assertTrue(a.belief_base == set([Literal.A, Literal.A >> Literal.B]) or a.belief_base == set([~Literal.B, Literal.A >> Literal.B]))
        self.assertTrue(postulates.test_all_postulates(before, a.belief_base, predict))

    def test_revision5(self):
        '''
        This test tests that revision can eliminate beliefs which entail ~phi only through many belief dirivations
        '''
        before = set([Literal.A, Literal.A >> Literal.B, Literal.B >> Literal.C])
        predict = ~Literal.C
        a = Agent(before)
        a.add_predict(predict)
        self.assertTrue(a.belief_base == set([~Literal.C, Literal.A, Literal.A >> Literal.B]) or a.belief_base == set([~Literal.C, Literal.A, Literal.B >> Literal.C]))
        self.assertTrue(postulates.test_all_postulates(before, a.belief_base, predict))

    def test_revision6(self):
        '''
        This test tests that revision can eliminate beliefs which entail ~phi only through many belief dirivations
        '''
        before = set([Literal.A, Literal.A >> Literal.B, Literal.B >> Literal.C, Literal.Q, Literal.Q >> Literal.P, Literal.P >> Literal.C])
        predict = ~Literal.C
        a = Agent(before)
        a.add_predict(predict)
        self.assertTrue(a.belief_base == set([~Literal.C, Literal.A, Literal.A >> Literal.B, Literal.Q, Literal.Q >> Literal.P]) or a.belief_base == set([~Literal.C, Literal.A, Literal.A >> Literal.B, Literal.Q, Literal.P >> Literal.C]) or a.belief_base == set([~Literal.C, Literal.A, Literal.B >> Literal.C, Literal.Q, Literal.Q >> Literal.P]) or a.belief_base == set([~Literal.C, Literal.A, Literal.B >> Literal.C, Literal.Q, Literal.P >> Literal.C]))
        self.assertTrue(postulates.test_all_postulates(before, a.belief_base, predict))

    def test_revision7(self):
        '''
        This test tests that when phi is a larger formula than the constintuates (the bb doesn't end up negating phi directly), the contradiction is still detected and removed
        '''
        before = set([Literal.A, Literal.B])
        predict = Literal.A >> ~Literal.B
        a = Agent(before)
        a.add_predict(predict)
        self.assertTrue(a.belief_base == set([Literal.A, Literal.A >> ~Literal.B]) or a.belief_base == set([Literal.B, Literal.A >> ~Literal.B]))
        self.assertTrue(postulates.test_all_postulates(before, a.belief_base, predict))

    def test_revision8(self):
        '''
        This test tests that when phi is a larger formula than the constintuates (the bb doesn't end up negating phi directly), the contradiction is still detected and removed
        '''
        before = set([Literal.A>>Literal.B, Literal.B>>Literal.A])
        predict = ~Literal.A
        a = Agent(before)
        a.add_predict(predict)
        # self.assertTrue(a.belief_base == set([~Literal.A, Literal.A>>Literal.B, Literal.B>>Literal.A]))
        self.assertTrue(postulates.test_all_postulates(before, a.belief_base, predict))

    def test_closure(self):
        a = Agent(set([Literal.P, Literal.P >> Literal.Q]))
        a.add_predict(Literal.Q)
        self.assertTrue(postulates.closure(a.belief_base, Literal.Q))

    def test_success(self):
        a = Agent(set([Literal.P, Literal.P >> Literal.Q]))
        a.add_predict(Literal.Q)
        self.assertTrue(postulates.success(a.belief_base, Literal.Q))

    def test_inclusion(self):
        a = Agent(set([Literal.P, Literal.P >> Literal.Q]))
        before = copy.deepcopy(a.belief_base)
        a.add_predict(Literal.Q)
        self.assertTrue(postulates.inclusion(before, a.belief_base, Literal.Q))

    def test_vacuity(self):
        a = Agent(set([Literal.P, Literal.P >> Literal.Q]))
        before = copy.deepcopy(a.belief_base)
        a.add_predict(Literal.Q)
        self.assertTrue(postulates.vacuity(before, a.belief_base, Literal.Q))

    def test_consistency(self):
        a = Agent(set([Literal.P, Literal.P >> Literal.Q]))
        a.add_predict(Literal.Q)
        self.assertTrue(postulates.consistency(a.belief_base, Literal.Q))

    def test_extensionality(self):
        a = Agent(set([Literal.P, Literal.P >> Literal.Q]))
        a.add_predict(Literal.Q)
        self.assertTrue(postulates.extensionality(a.belief_base, Literal.Q >> Literal.P, ~Literal.Q | Literal.P))



tester = MyTestCase()
tester.test_entailment()
tester.test_entailment2()

tester.test_revision1()
tester.test_revision2()
tester.test_revision3()
tester.test_revision4()
tester.test_revision5()
tester.test_revision6()
tester.test_revision7()
tester.test_revision8()