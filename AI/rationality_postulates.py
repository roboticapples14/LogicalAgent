import copy
import itertools
import sympy.logic as logic
from .Agent import Agent
from sympy.logic.boolalg import to_cnf

def closure(after, phi):
    """
    TODO: not required
    B ∗ φ = Cn(B ∗ φ)
    returns true if fulfilled and false if not fulfilled
    """
    check = False
    for belief in after:
        check = check or Agent.entailment(belief, phi)
    return not check

def success(after: set, phi):
    """
    the revised belief base contains phi
    """
    return after.__contains__(phi)

def inclusion(before: set, after: set, phi):
    """
    B ∗ φ ⊆ B + φ
    The belief base revised with phi, is a subset of belief base expanded with phi
    """
    before.add(phi)
    truth_sum = True
    for prop in list(after):
        truth_sum = before.__contains__(prop) & truth_sum
    return truth_sum

def vacuity(before: set, after: set, phi):
    """
    If ¬φ /∈ B, then B ∗ φ = B + φ
    If resolution passes on not phi, then the belief set revised with phi is equal to
    the belief set expanded with phi
    """
    # if resolution(before, phi), after should be before.add(phi)
    revisionBase = Agent(after)
    if revisionBase.resolution(~phi):
        expansionBase = copy.deepcopy(before)
        expansionBase.add(phi)
        return revisionBase.belief_base == expansionBase.belief_base
    return True

def consistency(after: set, phi):
    '''
    B ∗ φ is consistent if φ is consistent.
    if phi is consistent, after should be consistent
    '''
    a = Agent([])
    phi_cnf = to_cnf(phi)
    phi_set = a.get_clause_sets(phi_cnf)
    # check if phi is consistent
    phi_consistent = True
    for b in list(phi_set):
        phi_set.remove(b)
        a = Agent(list(phi_set))
        # check that the belief set has no conflict with b 
        phi_consistent = phi_consistent and a.resolution(list(b)[0])
        phi_set.append(set(b))

    # check if after is consistent
    after_consistent = True
    for b in list(after):
        after.remove(b)
        a = Agent(list(after))
        # check that the belief set has no conflict with b
        after_consistent = after_consistent and a.resolution(b)
        after.add(b)

    # if phi is consistent, after should be consistent
    # phi_consistent -> after_consistent
    return not phi_consistent or after_consistent

def extensionality(before, phi, psi):
    """
    Check if the biimplication of two formulas that should be revised with the belief base,
    is a tautology, if yes, check that the two resulting belief bases from revision are equal.
    """
    atoms_prop1 = phi.atoms()
    atoms_prop2 = psi.atoms()
    literals_in_props = atoms_prop1.union(atoms_prop2)
    permutations = list(itertools.product([True, False], repeat=len(list(literals_in_props))))
    literal_dict = {}
    logic_sum = True
    for p in permutations:
        for literal, value in zip(literals_in_props, list(p)):  # assign truth values to truth dict for current permutation of truth table
            literal_dict[literal] = value
        logic_sum = (((phi >> psi) & (psi >> psi)).subs(literal_dict)) & logic_sum

    if logic_sum is False:
        return True
    else:
        a = Agent(list(before))
        phi_revision = a.revision(before, phi)
        psi_revision = a.revision(before, phi)

        phi_mega_prop = to_cnf(list(phi_revision)[0])
        for prop in list(phi_revision)[1:]:
            phi_mega_prop = phi_mega_prop & to_cnf(prop)

        psi_mega_prop = to_cnf(list(psi_revision)[0])
        for prop in list(psi_revision)[1:]:
            psi_mega_prop = psi_mega_prop & to_cnf(prop)

        logic_sum = True
        for p in permutations:
            for literal, value in zip(literals_in_props, list(p)):  # assign truth values to truth dict for current permutation of truth table
                literal_dict[literal] = value
            logic_sum = ( (phi_mega_prop.subs(literal_dict)) == (psi_mega_prop.subs(literal_dict)) ) & logic_sum

        return logic_sum

def test_all_postulates(before: set, after: set, phi):
    succ = success(after, phi)
    inc = inclusion(before, after, phi)
    vacc = vacuity(before, after, phi)
    const = consistency(after, phi)
    return succ and inc and vacc and const