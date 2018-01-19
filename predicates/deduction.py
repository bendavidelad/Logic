""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/deduction.py """

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *


def inverse_mp(proof, assumption, print_as_proof_forms=False):
    """ Takes a proof, whose first six assumptions/axioms are Prover.AXIOMS, of
        a conclusion from a list of assumptions/axioms that contains the given
        assumption as a simple formula (i.e., without any templates), where no
        step of the proof is a UG step over a variable that is free in the
        given assumption, and returns a proof of (assumption−>conclusion) from
        the same assumptions except assumption """
    assert type(proof) is Proof
    assert proof.is_valid()
    assert type(assumption) is str
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions[:len(Prover.AXIOMS)] == Prover.AXIOMS
    # Task 11.1
    new_proof = Prover([x for x in proof.assumptions if x.formula.infix() != assumption],
                       Formula('->', Formula.parse(assumption), proof.conclusion))
    sub_dict = dict()
    for index, line in enumerate(proof.lines):
        if line.justification[0] is 'A':
            sub_dict[index] = a_helper(line, new_proof, proof, assumption)
        elif line.justification[0] is 'T':
            sub_dict[index] = t_helper(line, new_proof)
        elif line.justification[0] is 'MP':
            sub_dict[index] = \
                mp_helper(line, new_proof, assumption, sub_dict[line.justification[1]], sub_dict[
                    line.justification[2]])
        elif line.justification[0] is 'UG':
            sub_dict[index] = ug_helper(line, new_proof, sub_dict[line.justification[1]])
    return new_proof.proof


def mp_helper(line, new_proof, ass, antecedent_line, conditional_line):
    conclusion = '(' + ass + '->(' + line.formula.infix() + '))'
    return new_proof.add_tautological_inference(conclusion, [antecedent_line, conditional_line])


def t_helper(line, new_proof):
    return new_proof.add_tautology(line.formula)


def ug_helper(line, new_proof, just):
    sign = line.formula.variable
    quantified = 'A' + sign + '[' + new_proof.proof.lines[just].formula.infix() + ']'
    q = new_proof.proof.lines[just].formula.first.infix()
    r = new_proof.proof.lines[just].formula.second.infix()
    step1 = new_proof.add_ug(quantified, just)
    con = '((A' + sign + '[(' + q + '->' + r + ')]->(' + q + '->A' + sign + '[' + r + '])))'
    r2 = new_proof.proof.lines[just].formula.second.substitute({sign: Term('v')}).infix()
    step2 = new_proof.add_instantiated_assumption(con, Prover.US, {'x': sign, 'Q()': q, 'R(v)': r2})
    return new_proof.add_mp('(' + q + '->A' + sign + '[' + r + '])', step1, step2)


def a_helper(line, new_proof, old_proof, assumption):
    if old_proof.assumptions[line.justification[1]].formula.infix() == assumption:
        x = line.formula.infix()
        return new_proof.add_tautology('(' + assumption + '->' + x + ')')
    else:
        x = line.formula.infix()
        step1 = new_proof.add_instantiated_assumption(
            line.formula, old_proof.assumptions[line.justification[1]], line.justification[2])
        step2 = new_proof.add_tautology('(' + x + '->(' + assumption + '->' + x + '))')
        return new_proof.add_mp('(' + assumption + '->' + x + ')', step1, step2)


def proof_by_contradiction(proof, assumption, print_as_proof_forms=False):
    """ Takes a proof, whose first six assumptions/axioms are Prover.AXIOMS, of
        a contradiction (a formula whose negation is a tautology)  a list of
        assumptions/axioms that contains the given assumption as a simple
        formula (i.e., without any templates), where no step of the proof is a
        UG step over a variable that is free in the given assumption, and
        returns a proof of ~assumption from the same assumptions except
        assumption """
    assert type(proof) is Proof
    assert proof.is_valid()
    assert type(assumption) is str
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions[:len(Prover.AXIOMS)] == Prover.AXIOMS
    # Task 11.2
    new_proof = inverse_mp(proof, assumption)
    new_prover = Prover(new_proof.assumptions, new_proof.conclusion)
    step1 = new_prover.add_proof(new_proof.conclusion, new_proof)
    contradiction = new_proof.conclusion.second
    neg_contradiction = Formula("~", contradiction)
    neg_assumption = Formula("~", Formula.parse(assumption))
    first_applies = Formula("->", Formula.parse(assumption), contradiction)
    second_applies = Formula("->", neg_contradiction, neg_assumption)
    step2 = new_prover.add_tautology(Formula("->", first_applies, second_applies))
    step3 = new_prover.add_mp(second_applies, step1, step2)
    step4 = new_prover.add_tautology(neg_contradiction)
    step5 = new_prover.add_mp(neg_assumption, step4, step3)
    new_prover.proof.conclusion = new_prover.proof.lines[step5].formula
    return new_prover.proof
