""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/tautology.py """

from propositions.syntax import *
from propositions.proofs import *
from propositions.provers import MP, I1, I2, inverse_mp
from propositions.semantics import *

# Axiomatic Inference Rules (MP, I1, and I2 are imported from provers.py)

I3 = InferenceRule([], Formula.from_infix('(~p->(p->q))'))
NI = InferenceRule([], Formula.from_infix('(p->(~q->~(p->q)))'))
NN = InferenceRule([], Formula.from_infix('(p->~~p)'))
R = InferenceRule([], Formula.from_infix('((q->p)->((~q->p)->p))'))
A = InferenceRule([], Formula.from_infix('(p->(q->(p&q)))'))
NA1 = InferenceRule([], Formula.from_infix('(~p->~(p&q))'))
NA2 = InferenceRule([], Formula.from_infix('(~q->~(p&q))'))
O1 = InferenceRule([], Formula.from_infix('(p->(p|q))'))
O2 = InferenceRule([], Formula.from_infix('(q->(p|q))'))
NO = InferenceRule([], Formula.from_infix('(~p->(~q->~(p|q)))'))
T = InferenceRule([], Formula.from_infix('T'))
NF = InferenceRule([], Formula.from_infix('~F'))

AXIOMATIC_SYSTEM_IMPLIES_NOT = [MP, I1, I2, I3, NI, NN, R]
AXIOMATIC_SYSTEM = [MP, I1, I2, I3, NI, NN, A, NA1, NA2, O1, O2, NO, T, NF, R]


def prove_a(formula, lines, assum_dict):
    """
    handel the A cases
    :param formula: current formula to prove
    :param lines: current lines
    :return: lines that prove the formula
    """
    first_variable = formula.first
    second_variable = formula.second
    line1 = DeductiveProof.Line(
        Formula("->", first_variable, Formula("->", second_variable, Formula("&",
                                                                             first_variable,
                                                                             second_variable))), 6,
        [])
    line2 = DeductiveProof.Line(
        Formula("->", second_variable, Formula("&", first_variable, second_variable)), 0,
        [assum_dict[first_variable.infix()], len(lines)])
    line3 = DeductiveProof.Line(Formula("&", first_variable, second_variable), 0,
                                [assum_dict[second_variable.infix()], len(lines) + 1])
    return [line1, line2, line3]


def prove_na1(formula, lines, assum_dict):
    """
    handel the NA2 cases
    :param formula: current formula to prove
    :param lines: current lines
    :return: lines that prove the formula
    """
    first_variable = formula.first.first
    second_variable = formula.first.second
    line1 = DeductiveProof.Line(Formula("->", Formula("~", first_variable), Formula("~",
                                                                                    Formula("&",
                                                                                            first_variable,
                                                                                            second_variable))),
                                7, [])
    line2 = DeductiveProof.Line(Formula("~", Formula("&", first_variable, second_variable)), 0,
                                [assum_dict[Formula("~", first_variable).infix()], len(lines)])
    return [line1, line2]


def prove_na2(formula, lines, assum_dict):
    """
      handel the NA2 cases
      :param formula: current formula to prove
      :param lines: current lines
      :return: lines that prove the formula
      """
    first_variable = formula.first.first
    second_variable = formula.first.second
    line1 = DeductiveProof.Line(Formula("->", Formula("~", second_variable), Formula("~",
                                                                                     Formula("&",
                                                                                             first_variable,
                                                                                             second_variable))),
                                8, [])
    line2 = DeductiveProof.Line(Formula("~", Formula("&", first_variable, second_variable)), 0,
                                [assum_dict[Formula("~", second_variable).infix()], len(lines)])
    return [line1, line2]


def prove_o1(formula, lines, assum_dict):
    """
      handel the O1 cases
      :param formula: current formula to prove
      :param lines: current lines
      :return: lines that prove the formula
      """
    first_variable = formula.first
    second_variable = formula.second
    line1 = DeductiveProof.Line(
        Formula("->", first_variable, Formula("|", first_variable, second_variable)), 9, [])
    line2 = DeductiveProof.Line(Formula("|", first_variable, second_variable), 0,
                                [assum_dict[first_variable.infix()], len(lines)])
    return [line1, line2]


def prove_o2(formula, lines, assum_dict):
    """
      handel the O2 cases
      :param formula: current formula to prove
      :param lines: current lines
      :return: lines that prove the formula
      """
    first_variable = formula.first
    second_variable = formula.second
    line1 = DeductiveProof.Line(
        Formula("->", second_variable, Formula("|", first_variable, second_variable)), 10, [])
    line2 = DeductiveProof.Line(Formula("|", first_variable, second_variable), 0,
                                [assum_dict[second_variable.infix()], len(lines)])
    return [line1, line2]


def prove_no(formula, lines, assum_dict):
    """
      handel the NO cases
      :param formula: current formula to prove
      :param lines: current lines
      :return: lines that prove the formula
      """
    first_variable = formula.first.first
    second_variable = formula.first.second
    negate_first_variable = Formula("~", first_variable)
    negate_second_variable = Formula("~", second_variable)
    line1 = DeductiveProof.Line(Formula("->", negate_first_variable,
                                        Formula("->", negate_second_variable,
                                                Formula("~", Formula("|",
                                                                     first_variable,
                                                                     second_variable)))), 11, [])
    line2 = DeductiveProof.Line(Formula("->", negate_second_variable, Formula("~", Formula("|",
                                                                                           first_variable,
                                                                                           second_variable))),
                                0, [assum_dict[negate_first_variable.infix()], len(lines)])
    line3 = DeductiveProof.Line(Formula("~", Formula("|", first_variable, second_variable)), 0,
                                [assum_dict[negate_second_variable.infix()], len(lines) + 1])
    return [line1, line2, line3]


def prove_imp_I1(formula, lines, assumptions_dict, model):
    """
    handel the I1 cases
    :param formula: current formula to prove
    :param lines: current lines
    :param assumptions_dict: -
    :param model: -
    :return: lines that prove the formula
    """
    line_len = len(lines)
    line1 = DeductiveProof.Line(Formula(IMP, formula.second, formula), 1, [])
    if formula.second.infix() in assumptions_dict:
        line2 = DeductiveProof.Line(formula, 0,
                                    [assumptions_dict[formula.second.infix()], line_len])
        return [line1, line2]
    else:
        if formula.second == Formula('T'):
            # new_lines = implies_not_helper(formula.first, model, lines + [line1], assumptions_dict)
            new_lines = [(DeductiveProof.Line(Formula("T"), 12, []))]
            # new_lines.append(DeductiveProof.Line(Formula(IMP, Formula("T"), formula), 1, []))
            index1 = line_len + len(new_lines) - 1
            index2 = index1 + 1
            line2 = DeductiveProof.Line(formula, 0, [index1, index2])
            return new_lines + [line1, line2]
        else:
            new_lines = implies_not_helper(formula.second, model, lines + [line1], assumptions_dict)
            index1 = line_len + len(new_lines) - 1
            index2 = index1 + 2
            line2 = DeductiveProof.Line(formula, 0, [index1, index2])
            return new_lines + [line1, line2]


def prove_imp_I3(formula, lines, assumptions_dict, model):
    """
     handel the I3 cases
     :param formula: current formula to prove
     :param lines: current lines
     :param assumptions_dict: -
     :param model: -
     :return: lines that prove the formula
     """
    if NOT + formula.first.infix() in assumptions_dict.keys():
        first_variable = formula.first
        second_variable = formula.second
        line1 = DeductiveProof.Line(
            Formula("->", Formula("~", first_variable), formula), 3, [])
        line2 = DeductiveProof.Line(Formula("->", first_variable, second_variable), 0,
                                    [assumptions_dict[Formula("~", first_variable).infix()], len(lines)])
        return [line1, line2]
    else:
        new_lines = implies_not_helper(Formula(NOT, formula.first), model, lines, assumptions_dict)
        if formula.first == Formula('F'):
            new_lines.append(DeductiveProof.Line(Formula(NOT, Formula("F")), 13, []))
            new_lines.append(DeductiveProof.Line(Formula(IMP, Formula(NOT, Formula("F")), formula), 3, []))
            index1 = len(lines) + len(new_lines) - 2
            index2 = index1 + 1
            return new_lines + [DeductiveProof.Line(formula, 0, [index1, index2])]

        else:
            new_lines = new_lines + [
                DeductiveProof.Line(Formula(IMP, Formula(NOT, formula.first), formula), 3, [])]
            index1 = len(lines) + len(new_lines) - 2
            index2 = index1 + 1
            return new_lines + [DeductiveProof.Line(formula, 0, [index1, index2])]


def prove_imp_I3_implies_not(formula, lines, assumptions_dict, model):
    """
   handel the I3 cases for implies_not
   :param formula: current formula to prove
   :param lines: current lines
   :param assumptions_dict: -
   :param model: -
   :return: lines that prove the formula
   """
    index2 = len(lines)
    new_lines = []
    index1 = 0
    if formula.first.root == NOT:
        new_lines = prove_double_neg(Formula(NOT, formula.first), lines, assumptions_dict, model)
        line1 = DeductiveProof.Line(Formula(IMP, Formula(NOT, formula.first), formula), 3, [])
        new_lines.append(line1)
        index1 = index2 + 1
        index2 += 2
    elif NOT + formula.first.infix() in assumptions_dict.keys():
        index1 = assumptions_dict[NOT + formula.first.infix()]
        new_lines = [DeductiveProof.Line(Formula(IMP, Formula(NOT, formula.first), formula), 3, [])]
    elif not evaluate(formula.first, model):
        new_lines = prove_in_model_helper(Formula(NOT, formula.first), model, lines, assumptions_dict)
        new_lines = new_lines + [
            DeductiveProof.Line(Formula(IMP, Formula(NOT, formula.first), formula), 3, [])]
        index1 = index2 + len(new_lines) - 2
        index2 = index1 + 1
    return new_lines + [DeductiveProof.Line(formula, 0, [index1, index2])]


def prove_imp_NI(formula, lines, assumptions_dict, model):
    """
    handel the NI cases
    :param formula: current formula to prove
    :param lines: current lines
    :param assumptions_dict: -
    :param model: -
    :return: lines that prove the formula
    """
    lines_len = len(lines)
    first, second = formula.first.first, formula.first.second
    temp1 = Formula(NOT, Formula(IMP, first, second))

    temp2 = Formula(IMP, Formula(NOT, second), temp1)
    line1 = DeductiveProof.Line(Formula(IMP, first, temp2), 4, [])
    line2 = DeductiveProof.Line(temp2, 0, [assumptions_dict[first.infix()], lines_len])
    if NOT + second.infix() in assumptions_dict.keys():
        index2 = assumptions_dict[NOT + second.infix()]
        return [line1, line2, DeductiveProof.Line(temp1, 0, [index2, lines_len + 1])]
    else:
        line3 = implies_not_helper(temp2.first, model, lines + [line1, line2], assumptions_dict)
        line4 = DeductiveProof.Line(temp1, 0, [lines_len + len(line3) + 1, lines_len + 1])
        return [line1, line2] + line3 + [line4]


def prove_double_neg(formula, lines, assumptions_dict, model):
    """
    handel the double negative cases
    :param formula: current formula to prove
    :param lines: current lines
    :param assumptions_dict: -
    :param model: -
    :return: lines that prove the formula
    """
    lines_len = len(lines)

    line1 = [DeductiveProof.Line(Formula(IMP, formula.first.first, formula), 5, [])]
    if formula.first.first.infix() in assumptions_dict:
        line2 = [DeductiveProof.Line(formula, 0,
                                     [assumptions_dict[formula.first.first.infix()], lines_len])]
        return line1 + line2
    else:
        new_lines = implies_not_helper(formula.first.first, model, lines + [line1],
                                       assumptions_dict)
        new_lines.append(DeductiveProof.Line(formula, 0, [lines_len + len(new_lines), lines_len]))
        return line1 + new_lines


def add_to_assumption_dict(assumption_dict, new_l):
    """
    handles the insertion of new assumptions assumptions dictionary
    :param assumption_dict: current assumption_dict
    :param new_l: where the conclusions are taken from
    :return: new assumption_dict
    """
    if new_l:
        size = len(assumption_dict)
        reducer = 0
        for i, line in enumerate(new_l):
            conclusion = line.conclusion.infix()
            if conclusion not in assumption_dict:
                assumption_dict[conclusion] = size + i - reducer
            else:
                reducer += 1
    return assumption_dict


def prove_in_model_implies_not(formula, model):
    """ Return a proof of formula via AXIOMATIC_SYSTEM_IMPLIES_NOT from the
        assumptions that all variables are valued as in model, with the
        assumptions being ordered alphabetically by the names of the variables.
        It is assumed that formula is true in model, and may only have the
        operators implies and not in it """
    lines = []
    assumptions_dict = dict()
    assumptions_list = []
    # put the sorted assumptions in the proof and negate if necessary
    for index, assumption in enumerate(sorted(list(model.keys()))):
        if not model[assumption]:
            lines.append(DeductiveProof.Line(Formula.from_infix("~" + assumption)))
            assumptions_dict["~" + assumption] = index
            assumptions_list.append(formula.from_infix("~" + assumption))
        else:
            lines.append(DeductiveProof.Line(Formula.from_infix(assumption)))
            assumptions_dict[assumption] = index
            assumptions_list.append(formula.from_infix(assumption))
    # get proof lines and statement
    statement = InferenceRule(assumptions_list, formula)
    lines = lines + implies_not_helper(formula, model, lines, assumptions_dict)
    proof = DeductiveProof(statement, AXIOMATIC_SYSTEM_IMPLIES_NOT, lines)
    return proof


def implies_not_helper(formula, model, lines, assumption_dict):
    """
    handles the recursive part of prove_in_model_implies_not
    :param formula:  the current formula
    :param model: the current model
    :param lines: the proof current lines
    :param assumption_dict: the assumptions used by the proof
    :return:  the new lines for the proof
    """
    # end case for the recursion
    new_lines = []
    if formula.infix() in assumption_dict.keys():
        return new_lines
    elif is_unary(formula.root):
        if formula.first.root == IMP:
            new_lines = implies_not_helper(formula.first.first, model, lines + new_lines, assumption_dict) + \
                        implies_not_helper(formula.first.second, model, lines + new_lines, assumption_dict)
            assumption_dict = add_to_assumption_dict(assumption_dict, new_lines)
            new_lines = new_lines + prove_imp_NI(formula, lines + new_lines, assumption_dict, model)
        elif is_unary(formula.first.root):
            new_lines = implies_not_helper(formula.first.first, model, lines + new_lines, assumption_dict)
            assumption_dict = add_to_assumption_dict(assumption_dict, new_lines)
            new_lines = new_lines + prove_double_neg(formula, lines + new_lines, assumption_dict, model)
        elif formula.first.infix() in model:
            return []
    elif formula.root == IMP:
        # if theta_1 is negative
        if not evaluate(formula.first, model):
            new_lines = implies_not_helper(formula.first, model, lines + new_lines, assumption_dict) + \
                        implies_not_helper(formula.second, model, lines + new_lines, assumption_dict)
            assumption_dict = add_to_assumption_dict(assumption_dict, new_lines)
            new_lines = new_lines + prove_imp_I3_implies_not(formula, lines + new_lines, assumption_dict,
                                                             model)
        # if theta_2 is positive
        elif evaluate(formula.second, model):
            new_lines = implies_not_helper(formula.second, model, lines + new_lines, assumption_dict)
            assumption_dict = add_to_assumption_dict(assumption_dict, new_lines)
            new_lines = new_lines + prove_imp_I1(formula, lines + new_lines, assumption_dict, model)
    return new_lines


def reduce_assumption(proof_true, proof_false):
    """ Return a proof of the same formula that is proved in both proof_true
        and proof_false, via the same inference rules used in both proof_true
        and proof_false, from the assumptions common to proof_true and
        proof_false. The first three of the inference rules in the given proofs
        are assumed to be M,I1,I2, any additional inference rules are assumed
        to have no assumptions, the inference rules in the given proofs are
        assumed to contain R, and the assumptions of both proofs are assumed to
        coincide, except for the last assumption, where that of proof_false is
        the negation of that of proof_true """
    # find the assumption to remove from proof
    for i in range(len(proof_false.statement.assumptions)):
        if proof_true.statement.assumptions[i] != proof_false.statement.assumptions[i]:
            part1 = inverse_mp(proof_true, proof_true.statement.assumptions[i])
            part2 = inverse_mp(proof_false, proof_false.statement.assumptions[i])
            ass = proof_true.statement.assumptions[:i] + proof_true.statement.assumptions[i + 1:]
            statement = InferenceRule(ass, proof_true.statement.conclusion)

    x = Formula(IMP, part2.statement.conclusion, part2.statement.conclusion.second)
    part2_len, part1_len = len(part2.lines), len(part1.lines)
    # renumber the assumptions of the second part
    for line in part2.lines:
        if line.justification is not None:
            for i, just in enumerate(line.justification):
                line.justification[i] = just + part1_len
    # get the additional lines for the proof
    line1 = DeductiveProof.Line(Formula(IMP, part1.statement.conclusion, x), proof_false.rules.index(R), [])
    line2 = DeductiveProof.Line(x, 0, [part1_len - 1, part1_len + part2_len])
    line3 = DeductiveProof.Line(part2.statement.conclusion.second, 0,
                                [part1_len + part2_len - 1, part1_len + part2_len + 1])

    return DeductiveProof(statement, proof_true.rules, part1.lines + part2.lines + [line1, line2, line3])


def proof_or_counterexample_implies_not(formula):
    """ Return either a proof of formula via AXIOMATIC_SYSTEM_IMPLIES_NOT, or a
        model where formula does not hold. It is assumed that formula may only
        have the operators implies and not in it """
    model_list = []
    model_list2 = []
    # check if formula holds for all models
    for model in all_models(formula.variables()):
        if not evaluate(formula, model):
            return model
        else:
            model_list.append(model)
    # keep the model list sorted
    for key in sorted(model.keys(), reverse=True):
        model_list2 = sorted(model_list, key=lambda k: k[key])
    model_list = model_list2
    proof_list = []
    # get proofs for all models and reduce couples
    for i in range(0, len(model_list), 2):
        first = prove_in_model_implies_not(formula, model_list[i + 1])
        second = prove_in_model_implies_not(formula, model_list[i])
        proof_list.append(reduce_assumption(first, second))
    # reduce the proofs until only one left
    while len(proof_list) > 1:
        proof_list = sorted(proof_list, key=lambda k: k.statement.assumptions[0].infix(), reverse=True)
        temp_proof_list = []
        for i in range(0, len(proof_list), 2):
            p_first = proof_list[i + 1]
            p_second = proof_list[i]
            temp_proof_list.append(reduce_assumption(p_first, p_second))
        proof_list = temp_proof_list
    return proof_list[0]


def prove_in_model(formula, model):
    """ Return a proof of formula via AXIOMATIC_SYSTEM from the assumptions
        that all variables are valued as in model, with the assumptions being
        ordered alphabetically by the names of the variables. It is assumed
        that formula is true in model """
    # Task 6.4
    lines = []
    assumptions_dict = dict()
    assumptions_list = []
    # put the sorted assumptions in the proof and negate if necessary
    for index, assumption in enumerate(sorted(list(model.keys()))):
        if not model[assumption]:
            lines.append(DeductiveProof.Line(Formula.from_infix("~" + assumption)))
            assumptions_dict["~" + assumption] = index
            assumptions_list.append(formula.from_infix("~" + assumption))
        else:
            lines.append(DeductiveProof.Line(Formula.from_infix(assumption)))
            assumptions_dict[assumption] = index
            assumptions_list.append(formula.from_infix(assumption))
    # get proof lines and statement
    statement = InferenceRule(assumptions_list, formula)
    lines = lines + prove_in_model_helper(formula, model, lines, assumptions_dict)
    proof = DeductiveProof(statement, AXIOMATIC_SYSTEM, lines)
    return proof


def prove_in_model_helper(formula, model, lines, assum_dict):
    """
    handles the recursive part of prove_in_model
    :param formula:  the current formula
    :param model: the current model
    :param lines: the proof current lines
    :param assum_dict: the assumptions used by the proof
    :return:  the new lines for the proof
    """
    # end case for the recursion
    new_l = []
    if formula.infix() in assum_dict.keys():
        return new_l
    elif is_unary(formula.root):
        if formula.first.root == IMP:
            new_l = prove_in_model_helper(formula.first.first, model, lines, assum_dict)
            new_l = new_l + prove_in_model_helper(Formula("~", formula.first.second), model,
                                                  lines + new_l, assum_dict)
            assum_dict = add_to_assumption_dict(assum_dict, new_l)
            new_l = new_l + prove_imp_NI(formula, lines + new_l, assum_dict, model)
        elif formula.first.root == AND:
            if not evaluate(formula.first.first, model):
                new_l = prove_in_model_helper(Formula("~", formula.first.first), model, lines,
                                              assum_dict)
                assum_dict = add_to_assumption_dict(assum_dict, new_l)
                new_l = new_l + prove_na1(formula, lines + new_l, assum_dict)
            else:
                new_l = new_l + prove_in_model_helper(Formula("~", formula.first.second), model,
                                                      lines + new_l,
                                                      assum_dict)
                assum_dict = add_to_assumption_dict(assum_dict, new_l)
                new_l = new_l + prove_na2(formula, lines + new_l, assum_dict)
        elif formula.first.root == OR:
            new_l = prove_in_model_helper(Formula("~", formula.first.first), model, lines,
                                          assum_dict)
            new_l = new_l + prove_in_model_helper(Formula("~", formula.first.second), model,
                                                  lines + new_l, assum_dict)
            assum_dict = add_to_assumption_dict(assum_dict, new_l)
            new_l = new_l + prove_no(formula, lines + new_l, assum_dict)
        elif is_unary(formula.first.root):
            new_l = prove_in_model_helper(formula.first.first, model, lines, assum_dict)
            assum_dict = add_to_assumption_dict(assum_dict, new_l)
            new_l = new_l + prove_double_neg(formula, lines + new_l, assum_dict, model)
        elif formula.first.infix() in model:
            return []
    elif formula.root == IMP:
        # if theta_1 is negative
        if not evaluate(formula.first, model):
            new_l = prove_in_model_helper(Formula("~", formula.first), model, lines, assum_dict)
            assum_dict = add_to_assumption_dict(assum_dict, new_l)
            new_l = new_l + prove_imp_I3(formula, lines + new_l, assum_dict, model)
        # if theta_2 is positive
        elif evaluate(formula.second, model):
            new_l = prove_in_model_helper(formula.second, model, lines + new_l, assum_dict)
            assum_dict = add_to_assumption_dict(assum_dict, new_l)
            new_l = new_l + prove_imp_I1(formula, lines + new_l, assum_dict, model)
        else:
            return []
    elif formula.root == AND:
        new_l = prove_in_model_helper(formula.first, model, lines, assum_dict)
        new_l = new_l + prove_in_model_helper(formula.second, model, lines + new_l, assum_dict)
        assum_dict = add_to_assumption_dict(assum_dict, new_l)
        new_l = new_l + prove_a(formula, lines + new_l, assum_dict)
    elif formula.root == OR:
        if evaluate(formula.first, model):
            new_l = prove_in_model_helper(formula.first, model, lines, assum_dict)
            assum_dict = add_to_assumption_dict(assum_dict, new_l)
            new_l = new_l + prove_o1(formula, lines + new_l, assum_dict)
        else:
            new_l = new_l + prove_in_model_helper(formula.second, model, lines + new_l, assum_dict)
            assum_dict = add_to_assumption_dict(assum_dict, new_l)
            new_l = new_l + prove_o2(formula, lines + new_l, assum_dict)
    add_to_assumption_dict(assum_dict, new_l)
    return new_l


def proof_or_counterexample(formula):
    """ Return either a proof of formula via AXIOMATIC_SYSTEM, or a model where
        formula does not hold """
    # Task 6.5
    model_list = []
    model_list2 = []
    # check if formula holds for all models
    for model in all_models(formula.variables()):
        if not evaluate(formula, model):
            return model
        else:
            model_list.append(model)
    # keep the model list sorted
    for key in sorted(model.keys(), reverse=True):
        model_list2 = sorted(model_list, key=lambda k: k[key])
    model_list = model_list2
    proof_list = []
    # get proofs for all models and reduce couples
    for i in range(0, len(model_list), 2):
        first = prove_in_model(formula, model_list[i + 1])
        second = prove_in_model(formula, model_list[i])
        assert first.is_valid()
        assert second.is_valid()
        proof_list.append(reduce_assumption(first, second))
    # reduce the proofs until only one left
    while len(proof_list) > 1:
        proof_list = sorted(proof_list, key=lambda k: k.statement.assumptions[0].infix(),
                            reverse=True)
        temp_proof_list = []
        for i in range(0, len(proof_list), 2):
            p_first = proof_list[i + 1]
            p_second = proof_list[i]
            temp_proof_list.append(reduce_assumption(p_first, p_second))
        proof_list = temp_proof_list
    return proof_list[0]


def get_models(rule):
    models = []
    for model in all_models(rule.conclusion.variables()):
        if evaluate(rule.conclusion, model):
            bol = True
            for ass in rule.assumptions:
                if not evaluate(ass, model):
                    bol = False
            if bol:
                models.append(model)
    return models


def proof_or_counterexample_for_inference(rule):
    """ Return either a proof of rule via AXIOMATIC_SYSTEM, or a model where
        rule does not hold """
    # Task 6.6
    if len(rule.assumptions) == 0:
        return proof_or_counterexample(rule.conclusion)
    formula = rule.assumptions[0]
    proof_assumptions = []
    proof_assumptions2 = dict()
    proof_assumptions3 = []
    for j, ass in enumerate(rule.assumptions):
        proof_assumptions.append(DeductiveProof.Line(ass))
        proof_assumptions2[ass.infix()] = j
    if len(proof_assumptions) > 1:
        proof_assumptions3.append(proof_assumptions[0])
    for i in range(1, len(proof_assumptions)):
        formula = Formula(AND, proof_assumptions[i].conclusion, proof_assumptions3[- 1].conclusion)
        line1 = DeductiveProof.Line(Formula(IMP, proof_assumptions[i].conclusion,
                                            Formula(IMP, proof_assumptions3[- 1].conclusion, formula)), 6, [])
        line2 = DeductiveProof.Line(Formula(IMP, proof_assumptions3[- 1].conclusion, formula), 0,
                                    [proof_assumptions2[proof_assumptions[i].conclusion.infix()],
                                     len(proof_assumptions)])
        line3 = DeductiveProof.Line(formula, 0,
                                    [proof_assumptions2[proof_assumptions3[- 1].conclusion.infix()],
                                     len(proof_assumptions) + 1])
        proof_assumptions3.append(DeductiveProof.Line(formula))
        proof_assumptions = proof_assumptions + [line1, line2, line3]
        proof_assumptions2[formula.infix()] = len(proof_assumptions) - 1

    formula = Formula(IMP, formula, rule.conclusion)
    proof = proof_or_counterexample(formula)
    if type(proof) is dict:
        return proof
    else:
        size = len(proof_assumptions)
        for line in proof.lines:
            for i in range(len(line.justification)):
                line.justification[i] = line.justification[i] + size

        proof.lines = proof_assumptions + proof.lines
        proof.statement = rule
        proof.lines.append(DeductiveProof.Line(rule.conclusion, 0, [size - 1, len(proof.lines) - 1]))
        return proof


def model_or_inconsistent(formulae):
    """ Return either a model where all of formulae hold, or a list of two
        proofs, both from formulae via AXIOMATIC_SYSTEM, the first of some
        formula and the second of the negation of the same formula """
    # Task 6.7
    iter_formulae = iter(formulae)
    conjunction = next(iter_formulae)
    for formula in iter_formulae:
        conjunction = Formula(AND, conjunction, formula)
    negate_conjunction = Formula(NOT, conjunction)
    if is_tautology(negate_conjunction):
        first_proof = proof_or_counterexample_for_inference(InferenceRule(formulae, conjunction))
        second_proof = proof_or_counterexample(negate_conjunction)
        second_proof.statement.assumptions = formulae
        return [first_proof, second_proof]
    else:
        for model in all_models(conjunction.variables()):
            all_formulae_true = True
            for formula in formulae:
                if not evaluate(formula, model):
                    all_formulae_true = False
                    break
            if all_formulae_true:
                return model
