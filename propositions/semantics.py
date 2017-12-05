""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/semantics.py """

from propositions.syntax import *
import math
import copy

AND = '&'
OR = '|'
IFF = '<->'
IMP = '->'
NOT = '~'
NAND = '-&'
NOR = '-|'
MUX = '?:'
FALSE = 'F'
TRUE = 'T'


def evaluate(formula, model):
    """ Return the truth value of the given formula in the given model """
    # Task 2.1
    if is_constant(formula.root):
        if formula.root == 'T':
            return True
        elif formula.root == 'F':
            return False
    elif is_variable(formula.root):
        return model[formula.root]
    elif is_unary(formula.root):
        return not evaluate(formula.first, model)
    elif is_binary(formula.root):
        if formula.root == '&':
            return evaluate(formula.first, model) and evaluate(formula.second, model)
        elif formula.root == '|':
            return evaluate(formula.first, model) or evaluate(formula.second, model)
        elif formula.root == '->':
            if evaluate(formula.first, model) and not evaluate(formula.second, model):
                return False
            else:
                return True
        elif formula.root == '<->':
            if (not evaluate(formula.first, model) and not evaluate(formula.second, model)) or (evaluate(formula.first, model) and evaluate(formula.second, model)):
                return True
            else:
                return False
        elif formula.root == '-&':
            if evaluate(formula.first, model) and evaluate(formula.second, model):
                return False
            else:
                return True
        elif formula.root == '-|':
            if not evaluate(formula.first, model) and not evaluate(formula.second, model):
                return True
            else:
                return False
    else:
        if evaluate(formula.first, model):
            return evaluate(formula.second, model)
        else:
            return evaluate(formula.third, model)


def all_models(variables):
    """ Return an iterator over all possible models over the variables in the
        given list of variables. The order of the models is lexicographic
        according to the order of the variables in the given list, where False
        precedes True """
    # Task 2.2
    list_of_models = []
    basic_model = {}
    list_of_variables = list(variables)
    number_of_variables = len(list_of_variables)
    for variable in list_of_variables:
        basic_model[variable] = False
    list_of_models.append(basic_model)
    number_of_models = (math.pow(2, number_of_variables)) - 1
    current_model = basic_model
    for model in range(int(number_of_models)):
        current_model = copy.deepcopy(current_model)
        current_variable_number = number_of_variables - 1
        while current_model[list_of_variables[current_variable_number]]:
            if current_variable_number < 0:
                break
            else:
                current_variable_number -= 1
        current_model[list_of_variables[current_variable_number]] = True
        while current_variable_number < number_of_variables - 1:
            current_variable_number += 1
            current_model[list_of_variables[current_variable_number]] = False
        list_of_models.append(current_model)
    return iter(list_of_models)


def truth_values(formula, models):
    """ Return a list of the truth values of the given formula in each model
        in the given list of models """
    # Task 2.3
    list_of_truth_values = []
    for model in models:
        list_of_truth_values.append(evaluate(formula, model))
    return list_of_truth_values


def is_tautology(formula):
    """ Return whether the given formula is a tautology """
    # Task 2.4
    list_of_truth_values = truth_values(formula, all_models(list(formula.variables())))
    for truth_value in list_of_truth_values:
        if not truth_value:
            return False
    return True


def print_truth_table(formula):
    """ Print the truth table of the given formula """
    # Task 2.5
    variables = list(formula.variables())
    sorted_variables = sorted(variables)
    print("|", end="")
    for variable in sorted_variables:
        print(" " + variable + " |", end="")
    print(" " + formula.infix() + " |")
    print("|", end="")
    for variable in sorted_variables:
        current_variable_hyphens = ""
        for letter in range(len(variable)):
            current_variable_hyphens += "-"
        print("-" + current_variable_hyphens + "-|", end="")
    formula_hyphens = ""
    for letter in range(len(formula.infix())):
        formula_hyphens += "-"
    print("-" + formula_hyphens + "-|")
    models = list(all_models(sorted_variables))
    values = truth_values(formula, models)
    formula_spaces = ""
    for letter in range(len(formula.infix()) - 1):
        formula_spaces += " "
    for model, value in zip(models, values):
        print("|", end="")
        for variable in sorted_variables:
            variable_spaces = ""
            for i in range(len(variable)):
                variable_spaces += " "
            if model[variable]:
                print(" T" + variable_spaces + "|", end="")
            else:
                print(" F" + variable_spaces +  "|", end="")
        if value:
            print(" T" + formula_spaces + " |")
        else:
            print(" F" + formula_spaces + " |")


def synthesize_for_model(model):
    """ Return a propositional formula that evaluates to True in the given
        model, and to False in any other model over the same variables """
    # Task 2.6
    keys = list(model.keys())
    propositional = keys[0]
    if not model[propositional]:
        propositional = "~" + propositional
    iterkeys = iter(keys)
    next(iterkeys)
    for key in iterkeys:
        if model[key]:
            propositional = "(" + propositional + "&" + key + ")"
        else:
            propositional = "(" + propositional + "&~" + key + ")"
    return Formula.from_infix(propositional)


def synthesize(models, values):
    """ Return a propositional formula that has the given list of respective
        truth values in the given list of models """
    # Task 2.7
    list_of_propositionals = []
    for model, value in zip(models, values):
        list_of_propositionals.append(synthesize_for_model(model))
    first_true = -1
    for i, value in enumerate(values):
        if value:
            first_true = i
            break
    if first_true == -1:
        first_key = ""
        for model in models:
            for key in model:
                first_key = key
                break
            break
        return Formula.from_infix("(" + first_key + "&~" + first_key + ")")
    complex_formula = list_of_propositionals[first_true]
    for prop in range(first_true + 1, len(values), 1):
        if values[prop]:
            complex_formula = Formula("|", complex_formula, list_of_propositionals[prop])
    return complex_formula


def evaluate_inference(rule, model):
    """ Return whether the given inference rule holds in the given model """
    #Task 4.2
    if len(rule.assumptions) == 0:
        return is_tautology(rule.conclusion)
    iter_assumps = iter(rule.assumptions)
    all_assumptions = next(iter_assumps)
    for assumption in iter_assumps:
        all_assumptions = Formula('&', all_assumptions, assumption)
    inference_rule = Formula('->', all_assumptions, rule.conclusion)
    return evaluate(inference_rule, model)


def is_tautological_inference(rule):
    """ Return whether the given inference rule is a semantically correct
        implication of its assumptions """
    # Task 4.3
    all_models_of_rule = all_models(rule.variables())
    for model in all_models_of_rule:
        if not evaluate_inference(rule, model):
            return False
    return True


