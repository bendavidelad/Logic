""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/functions.py """

from predicates.syntax import *
from predicates.semantics import *
from predicates.util import *
from itertools import permutations


def replace_functions_with_relations_in_model(model):
    """ Return a new model obtained from the given model by replacing every
        function meaning with the corresponding relation meaning (i.e.,
        (x1,...,xn) is in the meaning if and only if x1 is the output of the
        function meaning for the arguments x2,...,xn), assigned to a relation
        with the same name as the function, except that the first letter is
        capitalized """
    assert type(model) is Model
    # Task 8.2
    functions_names = list()
    model_copy = copy.deepcopy(model)
    for key in model_copy.meaning:
        if is_function(key):
            functions_names.append(key)
            current_map = model_copy.meaning[key]
            current_set = set()
            for kary_tuple in current_map:
                current_tuple = tuple(current_map[kary_tuple]) + kary_tuple
                current_set.add(current_tuple)
            model_copy.meaning[key] = current_set
    for function_name in functions_names:
        model_copy.meaning[function_name[0].upper() + function_name[1:]] = model_copy.meaning[function_name]
        del model_copy.meaning[function_name]
    return model_copy



def replace_relations_with_functions_in_model(model, original_functions):
    """ Return a new model original_model with function names
        original_functions such that:
        model == replace_functions_with_relations_in_model(original_model)
        or None if no such original_model exists """
    assert type(model) is Model
    # Task 8.3
    model_copy = copy.deepcopy(model)
    for original_func in original_functions:
        func_as_relation_name = original_func[0].upper() + original_func[1:]
        if func_as_relation_name not in model_copy.meaning:
            return None
        current_set = model_copy.meaning[func_as_relation_name]
        current_map = dict()
        for item in current_set:
            if item[1:] in current_map:
                return None
            current_map[item[1:]] = item[0]
        number_of_arguments = len(list(current_set)[0]) - 1
        for permutation in permutations(model.universe, number_of_arguments):
            if permutation not in current_map:
                return None
        model_copy.meaning[original_func] = current_map
        del model_copy.meaning[func_as_relation_name]
    return model_copy



def compile_term_helper(term, list_of_steps):
    for argument in range(len(term.arguments)):
        if is_function(term.arguments[argument].root):
            term.arguments[argument] = compile_term_helper(term.arguments[argument], list_of_steps).first
    formula_to_return = Formula("=", Term(next(fresh_variable_name_generator)), term)
    list_of_steps.append(formula_to_return)
    return formula_to_return


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
    term_copy = copy.deepcopy(term)
    list_of_steps = list()
    compile_term_helper(term_copy, list_of_steps)
    return list_of_steps

def replace_function_with_corresponding_variable(term, fresh_variable, function_to_change):
    for argument in range(len(term.arguments)):
        if term.arguments[argument] == function_to_change:
            term.arguments[argument] = fresh_variable
        else:
            if is_function(term.arguments[argument].root):
                replace_function_with_corresponding_variable(term.arguments[argument], fresh_variable, function_to_change)


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
    formula_copy = copy.deepcopy(formula)
    total_formula = formula_copy
    if is_constant(formula.root) or is_variable(formula.root):
        return formula
    elif is_equality(formula.root):
        first_steps = list()
        second_steps = list()
        if is_function(formula.first.root):
            first_steps = compile_term(formula.first)
        if is_function(formula.second.root):
            second_steps = compile_term(formula.second)
        for step in first_steps:
            new_relation = Formula(step.second.root[0].upper() + step.second.root[1:], [step.first] + step.second.arguments)
            if formula_copy.first == step.second:
                formula_copy.first = step.first
            else:
                replace_function_with_corresponding_variable(formula_copy.first, step.first, step.second)
            if is_equality(total_formula.root):
                total_formula = Formula("A", step.first.root, Formula("->", new_relation, total_formula))
            else:
                temp = total_formula
                while temp.predicate.second != formula_copy:
                    temp = temp.predicate.second
                temp.predicate.second = Formula("A", step.first.root, Formula("->", new_relation, formula_copy))
        for step in second_steps:
            new_relation = Formula(step.second.root[0].upper() + step.second.root[1:], [step.first] + step.second.arguments)
            if formula_copy.second == step.second:
                formula_copy.second = step.first
            else:
                replace_function_with_corresponding_variable(formula_copy.second, step.first, step.second)
            if is_equality(total_formula.root):
                total_formula = Formula("A", step.first.root, Formula("->", new_relation, total_formula))
            else:
                temp = total_formula
                while temp.predicate.second != formula_copy:
                    temp = temp.predicate.second
                temp.predicate.second = Formula("A", step.first.root, Formula("->", new_relation, formula_copy))
        return total_formula
    elif is_relation(formula.root):
        list_of_lists = list()
        for argument in formula_copy.arguments:
            if is_function(argument.root):
                current_list = compile_term(argument)
                list_of_lists.append(current_list)
        for list_of_steps in list_of_lists:
            for step in list_of_steps:
                new_relation = Formula(step.second.root[0].upper() + step.second.root[1:], [step.first] + step.second.arguments)
                replace_function_with_corresponding_variable(formula_copy, step.first, step.second)
                if is_relation(total_formula.root):
                    total_formula = Formula("A", step.first.root, Formula("->", new_relation, total_formula))
                else:
                    temp = total_formula
                    while temp.predicate.second != formula_copy:
                        temp = temp.predicate.second
                    temp.predicate.second = Formula("A", step.first.root, Formula("->", new_relation, formula_copy))
        return total_formula
    elif is_binary(formula.root):
        return Formula(formula.root, replace_functions_with_relations_in_formula(formula.first), replace_functions_with_relations_in_formula(formula.second))
    elif is_unary(formula.root):
        return Formula("~", replace_functions_with_relations_in_formula(formula.first))
    elif is_quantifier(formula.root):
        return Formula(formula.root, formula.variable, replace_functions_with_relations_in_formula(formula.predicate))




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
    list_of_formulae = list()
    total_list = list()
    for formula in formulae:
        list_of_formulae.append(replace_functions_with_relations_in_formula(Formula.parse(formula)))
    print()






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
    # Task 8.7
    lst = []
    for i, formula in enumerate(formulae):
        assert type(formula) is str
        if "=" in formula:
            lst.append(i)
    new_formulae = []
    names = set()
    for i in lst:
        current_formula = Formula.parse_with_SAME(formulae[i])
        new_formulae.append(current_formula.infix())
        names = names | current_formula.relations()
    new_formulae = new_formulae + replace_equality_with_SAME_extra_lines(names)
    return new_formulae


def replace_equality_with_SAME_extra_lines(names):

    j, count = 0, 1
    names_lst = [x[0] for x in list(names)]
    if names_lst[0] == SAME:
        j = 1
    for_all = 'Ax0[Ay0['
    implies_list_1 = names_lst[j] + '(x0'
    implies_list_2 = names_lst[j] + '(y0'
    same = 'SAME(x0,y0)'
    for i in range(len(names_lst)):
        if names_lst[i] != SAME:
            for_all = for_all + 'Ax' + str(i + 1) + '[Ay' + str(i + 1) + '['
            implies_list_1 = implies_list_1 + ',x' + str(i + 1)
            implies_list_2 = implies_list_2 + ',y' + str(i + 1)
            same = same + '&(SAME(x' + str(i + 1) + ',y' + str(i + 1) + ')'
            count += 1
    line = [for_all + '(' + same + ')' * count + '->(' + implies_list_1 + ')->' + implies_list_2 + '))' + (
            ']' * 2 * count)]
    return line + ['SAME(x,x)', '(SAME(x,y)->SAME(y,x))', '((SAME(x,y)&SAME(y,z))->SAME(x,z))']


def add_SAME_as_equality(model):
    """ Return a new model obtained from the given model by adding the relation
        SAME that behaves like equality """
    assert type(model) is Model
    # Task 8.8
    new_model = copy.deepcopy(model)
    same_set = set()
    for i in model.universe:
        same_set.add((i, i))
    new_model.meaning[SAME] = same_set
    return new_model


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
    new_model = copy.deepcopy(model)
    remove_set1, remove_set2 = set(), set()
    for mean1 in new_model.meaning:
        if mean1 == SAME:
            for same in new_model.meaning[mean1]:
                if same[0] != same[1] and ((same[1], same[0]) not in remove_set1):
                    remove_set1.add(same)
    del new_model.meaning[SAME]

    for remove_tuple in remove_set1:
        if remove_tuple[0] in new_model.universe and remove_tuple[1] in new_model.universe:
            new_model.universe.remove(remove_tuple[0])
            for mean2 in new_model.meaning:
                if is_variable(mean2) or is_constant(mean2):
                    if new_model.meaning[mean2] == remove_tuple[0]:
                        new_model.meaning[mean2] = remove_tuple[1]
                else:
                    for relation_del in new_model.meaning[mean2]:
                        if relation_del[0] == remove_tuple[0]:
                            remove_set2.add((mean2, relation_del))
    for to_del in remove_set2:
        new_model.meaning[to_del[0]].remove(to_del[1])

    return new_model
