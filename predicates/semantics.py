""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/semantics.py """

from predicates.syntax import *
import copy
import math

class Model:
    """ A model for first-order formulae: contains a universe - a set of
        elements, and a dictionary that maps every constant name to an element,
        every k-ary relation name to a set of k-tuples of elements, and every
        k-ary function name to a map from k-tuples of elements to an element """

    def __init__(self, universe, meaning):
        assert type(universe) is set
        assert type(meaning) is dict
        self.universe = universe
        self.meaning = meaning

    def __repr__(self):
        return 'Universe=' + str(self.universe) + '; Meaning=' + str(self.meaning)
        
    def evaluate_term(self, term, assignment={}):
        """ Return the value of the given term in this model, where variables   
            get their value from the given assignment """
        assert term.variables().issubset(assignment.keys())
        # Task 7.7
        if is_constant(term.root):
            return self.meaning[term.root]
        elif is_variable(term.root):
            return assignment[term.root]
        else:
            arguments_evaluated = list()
            for argument in term.arguments:
                arguments_evaluated.append(self.evaluate_term(argument, assignment))
            return self.meaning[term.root][tuple(arguments_evaluated)]


    def evaluate_formula(self, formula, assignment={}):
        """ Return the value of the given formula in this model, where
            variables that are free in the formula get their values from the
            given assignment """
        assert formula.free_variables().issubset(assignment.keys())
        # Task 7.8
        if is_relation(formula.root):
            arguments_evaluated = list()
            for argument in formula.arguments:
                arguments_evaluated.append(self.evaluate_term(argument, assignment))
            return tuple(arguments_evaluated) in self.meaning[formula.root]
        elif is_equality(formula.root):
            return self.evaluate_term(formula.first, assignment) == self.evaluate_term(formula.second, assignment)
        elif is_quantifier(formula.root):
            current_assignment = copy.deepcopy(assignment)
            if formula.root == "A":
                for item in self.universe:
                    current_assignment[formula.variable] = item
                    if not self.evaluate_formula(formula.predicate, current_assignment):
                        return False
                return True
            elif formula.root == "E":
                for item in self.universe:
                    current_assignment[formula.variable] = item
                    if self.evaluate_formula(formula.predicate, current_assignment):
                        return True
                return False
        elif is_unary(formula.root):
            return not self.evaluate_formula(formula.first, assignment)
        else:
            if formula.root == "|":
                return self.evaluate_formula(formula.first, assignment) | self.evaluate_formula(formula.second, assignment)
            elif formula.root == "&":
                return self.evaluate_formula(formula.first, assignment) & self.evaluate_formula(formula.second, assignment)
            elif formula.root == "->":
                return (not self.evaluate_formula(formula.first, assignment)) & self.evaluate_formula(formula.second, assignment)

    def is_model_of(self, formulae_repr):
        """ Return whether self a model of the formulae represented by the
            given list of strings. For this to be true, each of the formulae
            must be satisfied, if the formula has free variables, then it must
            be satisfied for every assignment of elements of the universe to
            the free variables """
        # Task 7.9
        for formula_string in formulae_repr:
            current_formula = Formula.parse(formula_string)
            free_vars = current_formula.free_variables()
            all_models_of_free_vars = self.all_models(free_vars)
            for model in all_models_of_free_vars:
                if not self.evaluate_formula(current_formula, model):
                    return False
        return True

    def all_models(self, variables):
        """ Return an iterator over all possible models over the variables in the
            given list of variables. The order of the models is lexicographic
            according to the order of the variables in the given list, where False
            precedes True """
        # Task 2.2
        universe_as_list = list(self.universe)
        list_of_models = []
        basic_model = {}
        list_of_variables = list(variables)
        number_of_variables = len(list_of_variables)
        last_item = len(self.universe) - 1
        for variable in list_of_variables:
            basic_model[variable] = 0
        list_of_models.append(basic_model)
        number_of_models = (math.pow(len(self.universe), number_of_variables)) - 1
        current_model = basic_model
        for model in range(int(number_of_models)):
            current_model = copy.deepcopy(current_model)
            current_variable_number = number_of_variables - 1
            while current_model[list_of_variables[current_variable_number]] == last_item:
                if current_variable_number < 0:
                    break
                else:
                    current_variable_number -= 1
            current_model[list_of_variables[current_variable_number]] += 1
            while current_variable_number < number_of_variables - 1:
                current_variable_number += 1
                current_model[list_of_variables[current_variable_number]] = 0
            list_of_models.append(current_model)
        for model in list_of_models:
            for key in model:
                model[key] = universe_as_list[model[key]]
        return iter(list_of_models)


