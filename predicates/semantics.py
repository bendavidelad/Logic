""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/semantics.py """

from predicates.syntax import *
import copy

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
        # assert term.variables().issubset(assignment.keys())
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
            return self.evaluate_term(formula.first) == self.evaluate_term(formula.second)
        elif is_quantifier(formula.root):
            current_assignment = copy.deepcopy(assignment)
            if formula.root == "A":
                for item in self.universe:
                    current_assignment[formula.variable] = item
                    if not self.evaluate_formula(formula.predicate):
                        return False
                return True
            elif formula.root == "E":
                for item in self.universe:
                    current_assignment[formula.variable] = item
                    if self.evaluate_formula(formula.predicate):
                        return True
                return False
        elif is_unary(formula.root):
            return not self.evaluate_formula(formula.first, assignment)
        else:
            if formula.root == "|":
                return self.evaluate_formula(formula.first) | self.evaluate_formula(formula.second)
            elif formula.root == "&":
                return self.evaluate_formula(formula.first) & self.evaluate_formula(formula.second)
            elif formula.root == "->":
                return (not self.evaluate_formula(formula.first)) & self.evaluate_formula(formula.second)


    def is_model_of(self, formulae_repr):
        """ Return whether self a model of the formulae represented by the
            given list of strings. For this to be true, each of the formulae
            must be satisfied, if the formula has free variables, then it must
            be satisfied for every assignment of elements of the universe to
            the free variables """
        # Task 7.9
