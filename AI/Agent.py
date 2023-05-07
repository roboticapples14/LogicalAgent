import copy
import itertools
import sympy.abc as Literal
from sympy.logic.boolalg import to_cnf
from itertools import combinations
from sympy import Or, Symbol, Not, And, Implies
import sympy
from typing import Set, List, Tuple
import sys
sys.setrecursionlimit(5000)

class Agent:
    def __init__(self, belief_base):
        '''
        :param belief_set: List of initial propositions
        '''
        self.belief_base = belief_base  # List of propositions
        # self.alphabet = {}  # a dictionary of names to props

    def remove_duplicates(self, ls):
        '''
        takes a list and returns list without duplicates
        '''
        ls_of_frozensets = list(set(frozenset(item) for item in ls))
        return list(set(item) for item in ls_of_frozensets)

    def get_clause(self, prop):
        return to_cnf(prop).args

    @staticmethod
    def entailment(prop1, prop2):
        atoms_prop1 = prop1.atoms()
        atoms_prop2 = prop2.atoms()

        # cannot entail if no shared literals
        if (len(atoms_prop1.intersection(atoms_prop2)) == 0):
            return False

        literals_in_props = atoms_prop1.union(atoms_prop2)
        permutations = list(itertools.product([True, False], repeat=len(list(literals_in_props))))
        literal_dict = {}

        entailment_sum = True
        for p in permutations:
            for literal, value in zip(literals_in_props, list(p)):  # assign truth values to truth dict for current permutation of truth table
                literal_dict[literal] = value
            entailment_sum = ((prop1 >> prop2).subs(literal_dict)) and entailment_sum  # Using implication to check for entailment

        return entailment_sum

    def get_clause_sets(self, expr):
        '''
          : param prop: CNF form of our belief set
          : returns: set of sets representing clause Literals in each conjunction
          Goes through a CNF prop clause by clause and converts each conjuncted clause
          to set of literals
          Negations should be pushed into a
          The return value is free of dublicates
        '''
        if (isinstance(expr, (Symbol, Not))):
            return [set([expr])]

        if isinstance(expr, Or):
            return [set(expr.args)]

        megaset = []
        for clause in expr.args:
            if isinstance(clause, (Symbol, Not)):
                megaset.append(set([clause]))
            elif isinstance(clause, Or) or isinstance(clause, And):
                megaset.append(set(clause.args))
            else:
                megaset.append(set(clause.args) for clause in expr.clauses)

        return self.remove_duplicates(megaset)


    def reduce_operation(self, set1: Set[Symbol], set2: Set[Symbol]) -> List[Set[Symbol]]:
        '''
        : param set1, set2: takes 2 CNF sets
        : returns: the resolution of them
        '''
        result_set = set()
        set_2_cpy = set2.copy()
        didWork = False
        for l1 in set1:
            if set_2_cpy.__contains__(~l1):
                set_2_cpy.remove(~l1)
                didWork = True
                continue
            else:
                result_set.add(l1)

        return [set1, set_2_cpy] if not didWork else [result_set.union(set_2_cpy)]

    def resolution(self, phi, bb=None):
        '''
        To show that KB |= φ, we show that KB ∧ ¬φ is unsatisfiable.
        Add not phi to the belief base. Then add the first clause to mega_prop.
        The "for" loop goes over all the other cluses and add them with "and" operation between them.
        :returns: bool True if phi is accepted
        '''
        if bb == None:
            bb = self.belief_base

        bb_not_phi = list(bb)
        bb_not_phi.append(~phi)
        mega_prop = to_cnf(bb_not_phi[0])
        for prop in bb_not_phi[1:]:
            mega_prop = mega_prop & to_cnf(prop)
        clause_sets: List[Set[Symbol]] = self.get_clause_sets(mega_prop)

        def traverse(clause_sets: List[Set[Symbol]]):
            clause_combinations = list(combinations(clause_sets, 2))
            returnValue = False
            for combo in clause_combinations: # combo isinstance(Tuple[Set[Symbol]]
                set1, set2 = combo # set1, set2 isinstance(Set[Symbol])
                result: List[Set[Symbol]] = self.reduce_operation(set1, set2)
                if len(result) == 0:
                    returnValue = returnValue or True
                elif len(result) == 1:
                    tmpSet: List[Set[Symbol]] = copy.deepcopy(clause_sets)
                    tmpSet.remove(combo[0])
                    tmpSet.remove(combo[1])
                    tmpSet.append(set(result[0]))
                    tmpSet = self.remove_duplicates(tmpSet)
                    returnValue = False or traverse(tmpSet)
                else:
                    returnValue = returnValue or False
            return returnValue
        return traverse(clause_sets)

    def get_direct_contradictions(self, phi):
        contradictions = []
        for b in self.belief_base:
            if b == ~phi:
                contradictions.append(b)
        return contradictions

    def get_mega_prop(self, set1, set2):
        '''
        takes 2 sets of disjunctions and converts to a CNF mega prop
        '''
        set1_ls = list(set1)
        set2_ls = list(set2)
        set_1_symbol = set1_ls[0]
        set_2_symbol = set2_ls[0]
        for l in set1_ls[1:]:
            set_1_symbol = set_1_symbol | l
        for l in set2_ls[1:]:
            set_2_symbol = set_2_symbol | l
        return set_1_symbol & set_2_symbol

    def get_entailed_contradictions(self, phi):
        '''
        returns all sets of beliefs which entail ~phi
        1. gets all combos of beliefs
        2. for every combo, checks if the reduction results in ~phi. If so add combo to contradictions
        3. for any other result from reduction, create new combos from the deducted belief and continue evaluating
        '''
        contradictions = []
        bb = list(copy.deepcopy(self.belief_base))
        if bb == []:
            return []
        mega_prop = to_cnf(bb[0])
        for prop in bb[1:]:
            mega_prop = mega_prop & to_cnf(prop)
        clause_sets: List[Set[Symbol]] = self.get_clause_sets(mega_prop)

        # for all combinations of clause_sets, if reduce_operation results in ~phi, add clause set to contradictions
        clause_combinations = list(combinations(clause_sets, 2))
        
        # dictionary that keeps track of derived contradictions, and the beliefs they're derived from
        cc_dependencies = list(copy.deepcopy(clause_combinations))

        while len(clause_combinations) > 0:
            combo = clause_combinations.pop()
            set1, set2 = combo # set1, set2 isinstance(Set[Symbol])
            dependencies = list(cc_dependencies.pop()) 

            # im in hell
            if (not isinstance(set1, set)):
                set1 = {set1}
            if (not isinstance(set2, set)):
                set2 = {set2}
            
            # gets reduction of 2 clauses
            result: List[Set[Symbol]] = self.reduce_operation(set1, set2)

            # 2nd check: if set1 & set2 entails ~phi (in the case where phi is a more complex proposition than set1 and set2)
            # such as bb = {a, b} and phi = (a >> ~b), a and b will never reduce to ~phi explicitly
            mini_prop = self.get_mega_prop(set1, set2)
            entails_not_phi = self.entailment(mini_prop, ~phi)
            
            # if we get a contradiction
            if ~phi in result or entails_not_phi or (len(result) == 1 and len(result[0]) == 0):
            # if ~phi in result or entails_not_phi:
                contradictions.append(dependencies)
            # elif len(result) == 1 and len(result[0]) > 0:
            elif len(result) == 1:
                # we've derived a new belief from 2 others, so we add it to clause_combinations 
                # to be evaluated, and track it's dependencies of fundamental beliefs
                for b in clause_sets:
                    if (len(b) != 0):
                        clause_combinations.append( (b, result[0]) )
                        new_dependencies = copy.deepcopy(dependencies)
                        new_dependencies.append(b)
                        cc_dependencies.append(new_dependencies)
                        # clause_combinations = self.remove_duplicates(clause_combinations)
        return contradictions

    def intersection(self, BB1, BB2):
        '''
        takes the common beliefs between the belief bases
        '''
        if len(BB1) == 0 or len(BB2) == 0:
            return {}

        # if BB1 is already in CNF clause sets format
        if isinstance(BB1[0], set):
            clause_sets1: List[Set[Symbol]] = BB1
        else:
            bb1_list = list(BB1)
            mega_prop1 = to_cnf(bb1_list[0])
            for prop in bb1_list[1:]:
                mega_prop1 = mega_prop1 & to_cnf(prop)
            clause_sets1: List[Set[Symbol]] = self.get_clause_sets(mega_prop1)
        
        # if BB2 is already in CNF clause sets format
        if isinstance(BB2[0], set):
            clause_sets1: List[Set[Symbol]] = BB2
        else:
            bb2_list = list(BB2)
            mega_prop2 = to_cnf(bb2_list[0])
            for prop in bb2_list[1:]:
                mega_prop2 = mega_prop2 & to_cnf(prop)
            clause_sets2: List[Set[Symbol]] = self.get_clause_sets(mega_prop2)
        return [value for value in clause_sets1 if value in clause_sets2]

    def expansion(self, phi):
        '''
        get the belief_set and add phi to this
        '''
        self.belief_base = set(self.belief_base)
        self.belief_base.add(phi)

    def contraction(self, phi):
        """
        What we are now doing is:
        1. remove all direct contradictions
        2. finds all paird of beliefs which entail a contradiction, and eliminates an element in each from bb to remove the contradiction
        3. repeats until no more entailed contradictions are found
        """
        # remove any direct contradictions
        direct_contradictions = self.get_direct_contradictions(phi)
        self.belief_base = list(filter(lambda x: not direct_contradictions.__contains__(x), self.belief_base))

        entailed_contradictions: List[Set[Symbol]] = self.get_entailed_contradictions(phi)
        removed = []
        
        # for each entailed contradiction, remove one belief from it
        for c in entailed_contradictions:
            # convert the entailed contradictions out of CNF in order to remove the OG beliefs
            entailed_contradictions_in_bb = []
            for b in self.belief_base:
                if self.get_clause_sets(to_cnf(b))[0] in c:
                    entailed_contradictions_in_bb.append(b)
        
            index = self.get_index_of_biggest_prop(entailed_contradictions_in_bb)
            # only remove a belief if we haven't removed any from this combo yet
            if [b for b in removed if b in c] == []:
                self.belief_base.remove(entailed_contradictions_in_bb[index])
                removed.append(self.get_clause_sets(to_cnf(entailed_contradictions_in_bb[index]))[0])

    def get_index_of_biggest_prop(self, list_of_props):
        '''
        Heuristic is how many atoms in the proposition,
        This means that a more complex belief is less valuable.
        Building on the principle of fundamental laws are worth more
        '''
        index = 0
        current_prop_complexity = 0
        for i, prop in enumerate(list_of_props):
            atoms = prop.atoms()
            if len(list(atoms)) > current_prop_complexity:
                current_prop_complexity = len(list(atoms))
                index = i

        return index

    def revision(self, phi):
        """
        basically does levi identity
        """
        self.contraction(phi)
        self.expansion(phi)
        self.belief_base = set(self.belief_base)

    def add_predict(self, phi):
        '''

        '''
        if (self.belief_base == set() or self.resolution(phi)):
            self.expansion(phi)
        else:
            self.revision(phi)

if __name__ == "__main__":
    a = Agent(set([Literal.A & Literal.B]))
    print(a.entailment(Literal.A & Literal.B, Literal.C >> Literal.D))