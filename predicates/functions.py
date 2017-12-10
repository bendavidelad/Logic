""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/functions.py """

from predicates.syntax import *
from predicates.semantics import *
from predicates.util import *

def replace_functions_with_relations_in_model(model):
    """ Return a new model obtained from the given model by replacing every
        function meaning with the corresponding relation meaning (i.e.,
        (x1,...,xn) is in the meaning if and only if x1 is the output of the
        function meaning for the arguments x2,...,xn), assigned to a relation
        with the same name as the function, except that the first letter is
        capitalized """
    assert type(model) is Model
    # Task 8.2

def replace_relations_with_functions_in_model(model, original_functions):
    """ Return a new model original_model with function names
        original_functions such that:
        model == replace_functions_with_relations_in_model(original_model)
        or None if no such original_model exists """
    assert type(model) is Model
    # Task 8.3

def compile_term(term):
    """ Return a list of steps that result from compiling the given term,
        whose root is a function invocation (possibly with nested function
        invocations down the term tree). Each of the returned steps is a
        Formula of the form y=f(x1,...,xk), where the y is a new variable name
        obtained by calling next(fresh_variable_name_generator) (you may assume
        that such variables do not occur in the given term), f is a
        single function invocation, and each of the xi is either a constant or
        a variable. The steps should be ordered left-to-right between the
        arguments, and within each argument, the computation of a variable
        value should precede its usage. The left-hand-side variable of the last
        step should evaluate to the value of the given term """
    assert type(term) is Term and is_function(term.root)
    # Task 8.4

def replace_functions_with_relations_in_formula(formula):
    """ Return a function-free analog of the given formula. Every k-ary
        function that is used in the given formula should be replaced with a
        k+1-ary relation with the same name except that the first letter is
        capitalized (e.g., the function plus(x,y) should be replaced with the
        relation Plus(z,x,y) that stands for z=plus(x,y)). (You may assume
        that such relation names do not occur in the given formula, which
        furthermore does not contain any variables names starting with z.) The
        returned formula need only be equivalent to the given formula for
        models where each new relations encodes a function, i.e., is guaranteed
        to have single possible value for the first relation argument for every
        k-tuple of the other arguments """
    assert type(formula) is Formula
    # Task 8.5

def replace_functions_with_relations_in_formulae(formulae):
    """ Return a list of function-free formulae (as strings) that is equivalent
        to the given formulae list (also of strings) that may contain function
        invocations. This equivalence is in the following sense:
        for every model of the given formulae,
        replace_functions_with_relations_in_model(model) should be a model
        of the returned formulae, and for every model of the returned formulae,
        replace_relations_with_functions_in_model(model) should be a model
        of the given formulae. Every k-ary function that is used in the given
        formulae should be replaced with a k+1-ary relation with the same name
        except that the first letter is capitalized (e.g., the function
        plus(x,y) should be replaced with the relation Plus(z,x,y) that stands
        for z=plus(x,y)). (You may assume that such relation names do not occur
        in the given formulae, which furthermore does not contain any variables
        names starting with z.) The returned list should have one formula for
        each formula in the given list, as well as one additional formula for
        every relation that replaces a function name from the given list """
    for formula in formulae:
        assert type(formula) is str
    # task 8.6
        
def replace_equality_with_SAME(formulae):
    """ Return a list of equality-free formulae (as strings) that is equivalent
        to the given formulae list (also of strings) that may contain the
        equality symbol. Every occurrence of equality should be replaced with a
        matching instantiation of the relation SAME, which you may assume
        does not occur in the given formulae. You may assume that the given
        formulae do not contain any function invocations. The returned list
        should have one formula for each formula in the given list, as well as
        additional formulae that ensure that SAME is reflexive, symmetric,
        transitive, and respected by all relations in the given formulae """
    for formula in formulae:
        assert type(formula) is str
    # Task 8.7
        
def add_SAME_as_equality(model):
    """ Return a new model obtained from the given model by adding the relation
        SAME that behaves like equality """
    assert type(model) is Model
    # Task 8.8
    
def make_equality_as_SAME(model):
    """ Return a new model where equality is made to coincide with the
        reflexive, symmetric, transitive, and respected by all relations,
        relation SAME in the the given model. The requirement is that for every
        model and every list formulae_list, if we take
        new_formulae=replace_equality_with_SAME(formulae) and
        new_model=make_equality_as_SAME(model) then model is a valid model
        of new_formulae if and only if new_model is a valid model of formulae.
        The universe of the returned model should correspond to the equivalence
        classes of the SAME relation in the given model. You may assume that
        there are no function meanings in the given model """
    assert type(model) is Model
    # Task 8.9
