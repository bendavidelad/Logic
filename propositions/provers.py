""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/provers.py """

from functools import lru_cache

import copy

from propositions.syntax import *
from propositions.proofs import *

# Tautological Inference Rules
MP = InferenceRule([Formula.from_infix('p'), Formula.from_infix('(p->q)')],
                   Formula.from_infix('q'))

I1 = InferenceRule([], Formula.from_infix('(p->(q->p))'))
I2 = InferenceRule([], Formula.from_infix('((p->(q->r))->((p->q)->(p->r)))'))

N = InferenceRule([], Formula.from_infix('((~p->~q)->(q->p))'))

A1 = InferenceRule([], Formula.from_infix('(p->(q->(p&q)))'))
A2 = InferenceRule([], Formula.from_infix('((p&q)->p)'))
A3 = InferenceRule([], Formula.from_infix('((p&q)->q)'))

O1 = InferenceRule([], Formula.from_infix('(p->(p|q))'))
O2 = InferenceRule([], Formula.from_infix('(q->(p|q))'))
O3 = InferenceRule([], Formula.from_infix('((p->r)->((q->r)->((p|q)->r)))'))

T = InferenceRule([], Formula.from_infix('T'))

F = InferenceRule([], Formula.from_infix('~F'))

AXIOMATIC_SYSTEM = [MP, I1, I2, N, A1, A2, A3, O1, O2, O3, T, F]


@lru_cache(maxsize=1)  # Cache the return value of prove_implies_self
def prove_implies_self():
    """ Return a valid deductive proof for '(p->p)' via MP,I1,I2 """
    # Task 5.1
    rules = [MP, I1, I2]
    line0 = DeductiveProof.Line(Formula.from_infix("((p->((q->p)->p))->((p->(q->p))->(p->p)))"), 2, [])
    line1 = DeductiveProof.Line(Formula.from_infix("(p->((q->p)->p))"), 1, [])
    line2 = DeductiveProof.Line(Formula.from_infix("((p->(q->p))->(p->p))"), 0, [1, 0])
    line3 = DeductiveProof.Line(Formula.from_infix("(p->(q->p))"), 1, [])
    line4 = DeductiveProof.Line(Formula.from_infix("(p->p)"), 0, [3, 2])
    lines = [line0, line1, line2, line3, line4]
    return DeductiveProof(InferenceRule([], Formula.from_infix("(p->p)")), rules, lines)


def inverse_mp(proof, assumption):
    """ Return a valid deductive proof for '(assumption->conclusion)', where
        conclusion is the conclusion of proof, from the assumptions of proof
        except assumption, via MP,I1,I2 """
    # Task 5.3
    new_proof_lines = []
    assumptions_dict = {}
    original_assump_lines = lines_for_the_given_assumption(assumption)
    new_proof_lines.extend(original_assump_lines)
    for line in range(len(proof.lines)):
        if proof.lines[line].conclusion == assumption:
            assumptions_dict[line] = len(original_assump_lines) - 1
        elif proof.lines[line].rule is None or proof.lines[line].rule != 0:
            current_lines_to_add = lines_for_other_assumption_or_i1_or_i2(proof.lines[line], assumption, len(new_proof_lines))
            new_proof_lines.extend(current_lines_to_add)
            assumptions_dict[line] = len(new_proof_lines) - 1
        else:
            current_lines_to_add = lines_for_mp_rule(proof.lines[line], assumption, proof, len(new_proof_lines), assumptions_dict)
            new_proof_lines.extend(current_lines_to_add)
            assumptions_dict[line] = len(new_proof_lines) - 1
    updated_assumptions = copy.deepcopy(proof.statement.assumptions)
    updated_assumptions.remove(assumption)
    return DeductiveProof(InferenceRule(updated_assumptions, new_proof_lines[len(new_proof_lines) - 1].conclusion),
                                                                                        proof.rules, new_proof_lines)
    

def lines_for_the_given_assumption(assumption):
    proved_implies_self = prove_implies_self()
    proved_instance = prove_instance(proved_implies_self, InferenceRule([], Formula('->', assumption, assumption)))
    return proved_instance.lines


def lines_for_other_assumption_or_i1_or_i2(line, assumption, line_number):
    line1 = DeductiveProof.Line(line.conclusion, line.rule, line.justification)
    line2 = DeductiveProof.Line(Formula("->", line1.conclusion, Formula("->", assumption, line1.conclusion)), 1, [])
    line3 = DeductiveProof.Line(Formula("->", assumption, line1.conclusion), 0, [line_number,line_number + 1])
    return [line1, line2, line3]


def lines_for_mp_rule(line, assumption, proof, line_number, assumptions_dict):
    first_assumption = proof.lines[line.justification[0]].conclusion
    conclusion = line.conclusion
    line1 = DeductiveProof.Line(Formula("->", Formula("->", assumption, Formula("->", first_assumption,
                                            conclusion)), Formula("->", Formula("->", assumption,
                                           first_assumption), Formula("->", assumption, conclusion))), 2, [])
    line2 = DeductiveProof.Line(Formula("->", Formula("->", assumption, first_assumption),
                                        Formula("->", assumption, conclusion)), 0,
                                                            [assumptions_dict[line.justification[1]], line_number])
    line3 = DeductiveProof.Line(Formula("->", assumption, conclusion), 0,
                                                            [assumptions_dict[line.justification[0]], line_number + 1])
    return [line1, line2, line3]




@lru_cache(maxsize=1)  # Cache the return value of prove_hypothetical_syllogism
def prove_hypothetical_syllogism():
    """ Return a valid deductive proof for '(p->r)' from the assumptions
        '(p->q)' and '(q->r)' via MP,I1,I2 """
    # Task 5.4
    p_imples_q = Formula.from_infix("(p->q)")
    q_implies_r = Formula.from_infix("(q->r)")
    p = Formula.from_infix("p")
    statement = InferenceRule([p_imples_q, q_implies_r, p], Formula.from_infix("r"))
    line0 = DeductiveProof.Line(p_imples_q)
    line1 = DeductiveProof.Line(q_implies_r)
    line2 = DeductiveProof.Line(Formula.from_infix("p"))
    line3 = DeductiveProof.Line(Formula.from_infix("q"), 0, [2, 0])
    line4 = DeductiveProof.Line(Formula.from_infix("r"), 0, [3, 1])
    proof = DeductiveProof(statement, [MP, I1, I2], [line0, line1, line2, line3, line4])
    return inverse_mp(proof, Formula.from_infix("p"))

