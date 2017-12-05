""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/proofs.py """

from propositions.syntax import *
from propositions.semantics import *
from copy import deepcopy


class InferenceRule:
    """ An inference rule, i.e., a list of zero or more assumed formulae, and
        a conclusion formula """

    def __init__(self, assumptions, conclusion):
        assert type(conclusion) == Formula
        for assumption in assumptions:
            assert type(assumption) == Formula
        self.assumptions = assumptions
        self.conclusion = conclusion

    def __eq__(self, other):
        if (len(self.assumptions) != len(other.assumptions)):
            return False
        if self.conclusion != other.conclusion:
            return False
        for assumption1, assumption2 in zip(self.assumptions, other.assumptions):
            if assumption1 != assumption2:
                return False
        return True

    def __ne__(self, other):
        return not self == other

    def __repr__(self):
        return str([assumption.infix() for assumption in self.assumptions]) + \
               ' ==> ' + self.conclusion.infix()

    def variables(self):
        """ Return the set of atomic propositions (variables) used in the
            assumptions and in the conclusion of self. """

        variables_set = set()
        conclustion_vars = Formula.variables(self.conclusion)
        if len(conclustion_vars) > 0:
            variables_set.update(conclustion_vars)
        for assumption in self.assumptions:
            variables_set.update(Formula.variables(assumption))
        return variables_set

    def is_instance_of(self, rule, instantiation_map=None):
        """ Return whether there exist formulae f1,...,fn and variables
            v1,...,vn such that self is obtained by simultaneously substituting
            each occurrence of f1 with v1, each occurrence of f2 with v2, ...,
            in all of the assumptions of rule as well as in its conclusion.
            If so, and if instantiation_map is given, then it is (cleared and)
            populated with the mapping from each vi to the corresponding fi """
        new_dict = dict()
        if len(self.assumptions) != len(rule.assumptions):
            return False
        for formula, template in zip(self.assumptions, rule.assumptions):
            to_check = InferenceRule._update_instantiation_map(formula, template, new_dict)
            if not to_check:
                return False
        to_check = InferenceRule._update_instantiation_map(self.conclusion, rule.conclusion,
                                                           new_dict)
        if to_check:
            if instantiation_map is not None:
                instantiation_map.clear()
                instantiation_map.update(new_dict)
            return True
        return False

    @staticmethod
    def _update_instantiation_map(formula, template, instantiation_map):
        """ Return w hether the given formula can be obtained from the given
            template formula by simultaneously and consistantly substituting,
            for every variable in the given template formula, every occurrence
            of this variable with some formula, while respecting the
            correspondence already in instantiation_map (which maps from
            variables to formulae). If so, then instantiation_map is updated
            with any additional substitutions dictated by this matching. If
            not, then instantiation_map may be modified arbitrarily """
        if is_variable(template.root):
            if template.root in instantiation_map:
                if instantiation_map[template.infix()] == formula:
                    return True
                else:
                    return False
            else:
                instantiation_map[template.root] = formula
                return True
        elif formula.root == template.root:
            rec_func = InferenceRule._update_instantiation_map
            if is_unary(formula.root):
                return rec_func(formula.first, template.first, instantiation_map)
            elif is_ternary(formula.root):
                to_retrun = rec_func(formula.first, template.first, instantiation_map)
                to_retrun = to_retrun and rec_func(formula.second, template.second,
                                                   instantiation_map)
                to_retrun = to_retrun and rec_func(formula.third, template.third, instantiation_map)
                return to_retrun
            elif is_binary(formula.root):
                to_retrun = rec_func(formula.first, template.first, instantiation_map)
                to_retrun = to_retrun and rec_func(formula.second, template.second,
                                                   instantiation_map)
                return to_retrun
            else:
                return True  # its only the same constant
        else:
            return False


class DeductiveProof:
    """ A deductive proof, i.e., a statement of an inference rule, a list of
        assumed inference rules, and a list of lines that prove the former from
        the latter """

    class Line:
        """ A line, i.e., a formula, the index of the inference rule whose
            instance justifies the formula from previous lines, and the list
            of indices of these previous lines """

        def __init__(self, conclusion, rule=None, justification=None):
            self.conclusion = conclusion
            self.rule = rule
            self.justification = justification

        def __repr__(self):
            if (self.rule is None):
                return self.conclusion.infix()
            r = self.conclusion.infix() + ' (Inference Rule ' + str(self.rule)
            sep = ';'
            for i in range(len(self.justification)):
                r += sep + ' Assumption ' + str(i) + ': Line ' + \
                     str(self.justification[i])
                sep = ','
            r += '.)' if len(self.justification) > 0 else ')'
            return r

    def __init__(self, statement, rules, lines):
        self.statement = statement
        self.rules = rules
        self.lines = lines

    def __repr__(self):
        r = 'Proof for ' + str(self.statement) + ':\n'
        for i in range(len(self.rules)):
            r += 'Inference Rule ' + str(i) + ': ' + str(self.rules[i]) + '\n'
        for i in range(len(self.lines)):
            r += str(i) + ') ' + str(self.lines[i]) + '\n'
        return r

    def instance_for_line(self, line):
        """ Return the instantiated inference rule that corresponds to the
            given line number """
        lines_list = self.lines[line].justification
        assumption_list = []
        if lines_list is not None:
            for line_index in lines_list:
                assumption_list.append(self.lines[line_index].conclusion)
        conclusion = self.lines[line].conclusion
        return InferenceRule(assumption_list, conclusion)

    def is_valid(self):
        """ Return whether lines are a valid proof of statement from rules """
        for line in range(len(self.lines)):
            if self.lines[line].rule is None:
                if not self.lines[line].conclusion in self.statement.assumptions:
                    return False
            else:
                justification = self.lines[line].justification
                if justification is None:
                    return False
                elif len(justification) > 0 and (
                        line < max(justification) or min(justification) < 0):
                    x=self.lines[line]
                    return False
                inference_rule_to_check = self.instance_for_line(line)
                rule_to_check = self.rules[self.lines[line].rule]
                if not inference_rule_to_check.is_instance_of(rule_to_check):
                    inference_rule_to_check.is_instance_of(rule_to_check)
                    return False
        if len(self.lines) == 0:
            if self.statement.conclusion == Formula(TRUE) or \
                            self.statement.conclusion == Formula(NOT, Formula(FALSE)):
                return True
            else:
                return False
        if self.statement.conclusion == self.lines[len(self.lines) - 1].conclusion:
            return True
        return False


def instantiate(formula, instantiation_map):
    """ Return a formula obtained from the given formula by simultaneously
        substituting, for each variable v that is a key of instantiation_map,
        each occurrence v with the formula instantiation_map[v] """
    first, second, third = None, None, None
    if is_unary(formula.root):
        first = instantiate(formula.first, instantiation_map)
    elif is_binary(formula.root):
        first = instantiate(formula.first, instantiation_map)
        second = instantiate(formula.second, instantiation_map)
    elif is_ternary(formula.root):
        first = instantiate(formula.first, instantiation_map)
        second = instantiate(formula.second, instantiation_map)
        third = instantiate(formula.third, instantiation_map)
    elif is_variable(formula.root):
        if formula.root in instantiation_map:
            return deepcopy(instantiation_map[formula.root])
        else:
            return deepcopy(formula)

    return Formula(formula.root, first, second, third)


def change_InferenceRule(inference_rule, instantiation_map):
    conclusion = instantiate(inference_rule.conclusion, instantiation_map)
    index_len = len(inference_rule.assumptions)
    assumptions = []
    for assumption, index in zip(inference_rule.assumptions, range(index_len)):
        assumptions.append(instantiate(assumption, instantiation_map))
    return InferenceRule(assumptions, conclusion)


def prove_instance(proof, instance):
    """ Return a proof of the given instance of the inference rule that proof
        proves, via the same inference rules used by proof """
    tmp_dict = {}
    proof_deepcopy = deepcopy(proof)
    instance.is_instance_of(proof_deepcopy.statement, tmp_dict)
    proof_deepcopy.statement = change_InferenceRule(proof_deepcopy.statement, tmp_dict)
    for line, index in zip(proof_deepcopy.lines, range(len(proof_deepcopy.lines))):
        proof_deepcopy.lines[index].conclusion = instantiate(line.conclusion, tmp_dict)
    return proof_deepcopy


def inline_proof_creat_rules(main_proof, lemma_proof):
    """
    create a rule list for inline_proof without the statement of lemma_proof and without rules
    of lemma_proof that are instance of rules of main_proof
    :return: a list of rules
    """
    main_rule_list = []
    lemma_rule_dict, main_rule_dict = {}, {}
    found_rule = False
    replace_rule_index = -1
    for main_rule in main_proof.rules:
        if not main_rule.is_instance_of(lemma_proof.statement):
            main_rule_list.append(main_rule)
            main_rule_dict[main_proof.rules.index(main_rule)] = main_rule_list.index(main_rule)
        else:
            replace_rule_index = main_proof.rules.index(main_rule)
    for lemma_rule in lemma_proof.rules:
        for main_rule, index in zip(main_rule_list, range(len(main_rule_list))):
            if lemma_rule.is_instance_of(main_rule):
                found_rule = True
                lemma_rule_dict[lemma_proof.rules.index(lemma_rule)] = index
                break
        if not found_rule:
            main_rule_list.append(lemma_rule)
            lemma_rule_dict[lemma_proof.rules.index(lemma_rule)] = main_rule_list.index(lemma_rule)
        found_rule = False
    return main_rule_list, main_rule_dict, lemma_rule_dict, replace_rule_index


def inline_proof_lemma(main_proof, line_index, lemma_proof, lines, lemma_rule_dict, line_count,
                       main_lines_dict):
    """
    create the lines for replace a rule with a lemma
    :param main_proof: the full proof
    :param line_index: the index of the line in the original proof
    :param lemma_proof: the lemma proof
    :param lines: a list of lines in the new proof
    :param lemma_rule_dict: a dictionary to find the correct line of the lemma
    :param line_count: the current index for the latest line
    :param main_lines_dict: a dictionary to find the correct line in the new proof
    :return: the list of lines, th line counter and the main lines dictionary
    """
    inference_rule = main_proof.instance_for_line(line_index)
    new_proof = prove_instance(lemma_proof, inference_rule)
    lemma_line_dict = {}
    for lemma_line, lemma_line_index in zip(new_proof.lines, range(len(new_proof.lines))):
        if lemma_line.rule is None:
            for tmp_line, tmp_index in zip(lines, range(len(lines))):
                if tmp_line.conclusion == lemma_line.conclusion:
                    lemma_line_dict[lemma_line_index] = tmp_index
                    break
        else:
            lemma_line.rule = lemma_rule_dict[lemma_line.rule]
            for num, index in zip(lemma_line.justification,
                                  range(len(lemma_line.justification))):
                lemma_line.justification[index] = lemma_line_dict[num]
            lemma_line_dict[lemma_line_index] = line_count
            lines.append(lemma_line)
            line_count += 1
    main_lines_dict[line_index] = line_count - 1
    lemma_line_dict.clear()
    return lines, line_count, main_lines_dict


def inline_proof(main_proof, lemma_proof):
    """ Return a proof of the inference rule that main_proof proves, via the
        inference rules used in main_proof except for the one proven by
        lemma_proof, as well as via the inference rules used in lemma_proof
        (with duplicates removed) """
    main_proof, lemma_proof = deepcopy(main_proof), deepcopy(lemma_proof)
    rule_list, main_rule_dict, lemma_rule_dict, lemma_rule_index = inline_proof_creat_rules(
        main_proof, lemma_proof)
    lines = []
    line_count = 0
    main_lines_dict = {}
    for line, line_index in zip(main_proof.lines, range(len(main_proof.lines))):
        if line.rule is None:
            lines.append(line)
            main_lines_dict[line_index] = line_count
            line_count += 1
        elif line.rule != lemma_rule_index:
            main_lines_dict[line_index] = line_count
            line.rule = main_rule_dict[line.rule]
            for num, index in zip(line.justification, range(len(line.justification))):
                line.justification[index] = main_lines_dict[num]
            lines.append(line)
            line_count += 1
        else:
            lines, line_count, main_lines_dict = inline_proof_lemma(main_proof, line_index,
                                                                    lemma_proof, lines,
                                                                    lemma_rule_dict, line_count,
                                                                    main_lines_dict)
    return DeductiveProof(main_proof.statement, rule_list, lines)
