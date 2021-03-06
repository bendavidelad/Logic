""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/syntax.py """
import copy

from propositions.syntax import Formula as PropositionalFormula
from predicates.util import *
import copy

EQU = "="
SAME = 'SAME'


def is_unary(s):
    """ Is s a unary operator? """
    return s == '~'


def is_term(s):
    return type(s) is Term


def is_binary(s):
    """ Is s a binary boolean operator? """
    return s == '&' or s == '|' or s == '->'


def is_equality(s):
    """ Is s the equality relation? """
    return s == EQU


def is_quantifier(s):
    """ Is s a quantifier? """
    return s == "A" or s == "E"


def is_relation(s):
    """ Is s a relation name? """
    return s[0] >= 'F' and s[0] <= 'T' and s.isalnum()


def is_constant(s):
    """ Is s a constant name? """

    return ((s[0] >= '0' and s[0] <= '9') or (s[0] >= 'a' and s[0] <= 'd')) and s.isalnum()


def is_function(s):
    """ Is s a function name? """
    return s[0] >= 'f' and s[0] <= 't' and s.isalnum()


def is_variable(s):
    """ Is s a variable name? """
    return s[0] >= 'u' and s[0] <= 'z' and s.isalnum()


class Term:
    """ A term in a first order logical formula, composed from constant names
        and variable names, and function names applied to them """

    def __init__(self, root, arguments=None):
        if is_constant(root) or is_variable(root):
            assert arguments is None
            self.root = root
        else:
            assert is_function(root)
            for x in arguments:
                assert type(x) is Term
            self.root = root
            self.arguments = arguments

    def __repr__(self):
        """ Return the usual (functional) representation of self """
        # Task 7.1
        return self.infix()

    def __eq__(self, other):
        return str(self) == str(other)

    def __ne__(self, other):
        return not self == other

    def __hash__(self):
        return hash(str(self))

    def infix(self):
        """ Return an infix representation of self """
        if is_constant(self.root) or is_variable(self.root):
            return self.root
        elif is_function(self.root):
            x = self.arguments[0].infix()
            for i in self.arguments[1:]:
                x = x + ',' + i.infix()
            return self.root + '(' + x + ')'

    @staticmethod
    def parse_prefix(s):
        """ Parse a term from the prefix of a given string. Return a pair: the
            parsed term, and the unparsed remainder of the string """
        # Task 7.3.1
        if is_constant(s[0]) or is_variable(s[0]):
            i = 1
            while (is_constant(s[0:i]) or is_variable((s[0:i]))) and i < len(s):
                i += 1
            if s[i - 1] == ',' or s[i - 1] == ']':
                i -= 1
            return (Term(s[0:i])), s[i:]
        elif is_function(s[0]):
            i = 1
            while is_function(s[0:i]):
                i += 1
            i = i - 1
            name = s[0:i]
            opened_par = 0
            closed_par = 0
            lst = []
            last_comma = i
            while not (opened_par == closed_par != 0):
                if s[i] == "(":
                    opened_par += 1
                elif s[i] == ")":
                    closed_par += 1
                elif s[i] == "," and opened_par < closed_par + 2:
                    lst.append(Term.parse_prefix(s[last_comma + 1:i])[0])
                    last_comma = i
                i += 1
            lst.append(Term.parse_prefix(s[last_comma + 1:i - 1])[0])
            this_term = Term(name, lst)
            return [this_term, s[i:]]

    @staticmethod
    def parse(s):
        """ Return a term parsed from its given string representation """
        # Task 7.3.2
        res, s = Term.parse_prefix(s)
        while s != '':
            res, s = Term.parse_prefix(s)
        return res

    def variables(self):
        """ Return the set of variables in this term """
        # Task 7.5
        ret = set()
        if is_variable(self.root):
            return {self.root}

        elif is_function(self.root):
            for arg in self.arguments:
                ret = ret | arg.variables()
            return ret
        return ret

    def relations(self):
        """
        ends the recursion for Formula.relations(
        :return: an empty set
        """
        return set()

    def functions(self):
        """ Return a set of pairs (function_name, arity) for all function names
            that appear in this term """
        # Task 8.1.1
        ret = set()
        if is_function(self.root[0]):
            arity = len(self.arguments)
            ret.add((self.root, arity))
            for arg in self.arguments:
                ret = ret | arg.functions()
        return ret

    def substitute(self, substitution_map):
        """ Return a term obtained from this term where all the occurrences of
            each constant name or variable name element_name that appears as a
            key in the dictionary substitution_map are replaced with the term
            substitution_map[element_name] """
        # Task 9.1

        for element_name in substitution_map:
            assert (is_constant(element_name) or is_variable(element_name)) and \
                   type(substitution_map[element_name]) is Term
        if is_constant(self.root) or is_variable(self.root):
            if self.root in substitution_map:
                return substitution_map[self.root]
            return self
        else:
            new_term = self
            for i, term in enumerate(new_term.arguments):
                new_term.arguments[i] = term.substitute(substitution_map)
            return new_term


def unary(s):
    if EQU in s:
        if ']' in s:
            i = s.index(EQU)
            x = Formula.parse_prefix(s[i + 1:s.index(']')])
            y = Formula.parse_prefix(s[1:i])
            return [Formula(s[0], Formula(EQU, y[0], x[0])), ']']
        else:
            i = s.index(EQU)
            x = Formula.parse_prefix(s[i + 1:])
            y = Formula.parse_prefix(s[1:i])
            return [Formula(s[0], Formula(EQU, y[0], x[0])), x[1]]
    else:
        x = Formula.parse_prefix(s[1:])
        return [Formula(s[0], x[0]), x[1]]


def unary_SAME(s):
    if EQU in s:
        i = s.index(EQU)
        x = Formula.parse_prefix(s[i + 1:])
        y = Formula.parse_prefix(s[1:i])
        return [Formula(s[0], Formula(SAME, [y[0], x[0]])), x[1]]
    else:
        x = Formula.parse_prefix(s[1:])
        return [Formula(s[0], x[0]), x[1]]


def quantifier(s):
    i = 2
    while is_variable(s[1:i]):
        i += 1
    i = i - 1
    variable = s[1:i]
    opened_par, closed_par = 0, 0
    last_comma = i
    while not (opened_par == closed_par != 0):
        if s[i] == "[":
            opened_par += 1
        elif s[i] == "]":
            closed_par += 1
        i += 1
    predicate, reminder = Formula.parse_prefix(s[last_comma + 1:])
    if reminder:
        if reminder[0] == EQU:
            x = Term.parse_prefix(reminder[1:])
            predicate = Formula(EQU, predicate, x[0])
            reminder = x[1]
        elif is_binary(reminder[0]):
            x = Formula.parse_prefix(reminder[1:])
            predicate = Formula(reminder[0], predicate, x[0])
            reminder = x[1]
        elif is_binary(reminder[0:2]):
            x = Formula.parse_prefix(reminder[2:])
            predicate = Formula(reminder[0:2], predicate, x[0])
            reminder = x[1]
        return Formula(s[0], variable, predicate), reminder[1:]
    return Formula(s[0], variable, predicate), ''


def quantifier_SAME(s):
    i = 2
    while is_variable(s[1:i]):
        i += 1
    i = i - 1
    variable = s[1:i]
    opened_par, closed_par = 0, 0
    last_comma = i
    while not (opened_par == closed_par != 0):
        if s[i] == "[":
            opened_par += 1
        elif s[i] == "]":
            closed_par += 1
        i += 1
    predicate, reminder = Formula.parse_prefix_SAME(s[last_comma + 1:])
    if reminder[0] == EQU:
        x = Term.parse_prefix(reminder[1:])
        predicate = Formula(SAME, [predicate, x[0]])
        reminder = x[1]
    elif is_binary(reminder[0]):
        x = Formula.parse_prefix(reminder[1:])
        predicate = Formula(reminder[0], predicate, x[0])
        reminder = x[1]
    elif is_binary(reminder[0:2]):
        x = Formula.parse_prefix(reminder[2:])
        predicate = Formula(reminder[0:2], predicate, x[0])
        reminder = x[1]
    return Formula(s[0], variable, predicate), reminder[1:]


def function_or_relation(s):
    i = 1
    while (is_function(s[0:i]) or is_relation(s[0:i])) and i < len(s):
        i += 1
    i = i - 1
    name = s[0:i]
    opened_par = 0
    closed_par = 0
    lst = []
    last_comma = i
    while not (opened_par == closed_par != 0):
        if s[i] == "(":
            opened_par += 1
        elif s[i] == ")":
            closed_par += 1
        elif s[i] == "," and opened_par < closed_par + 2:
            lst.append(Formula.parse_prefix(s[last_comma + 1:i])[0])
            last_comma = i
        i += 1
    if last_comma + 1 != i - 1:
        lst.append(Formula.parse_prefix(s[last_comma + 1:i - 1])[0])
    if is_relation(s[0]):
        this_formula = Formula(name, lst)
        return [this_formula, s[i:]]
    else:
        this_term = Term(name, lst)
        return [this_term, s[i:]]


def function_or_relation_SAME(s):
    i = 1
    while (is_function(s[0:i]) or is_relation(s[0:i])) and i < len(s):
        i += 1
    i = i - 1
    name = s[0:i]
    opened_par = 0
    closed_par = 0
    lst = []
    last_comma = i
    while not (opened_par == closed_par != 0):
        if s[i] == "(":
            opened_par += 1
        elif s[i] == ")":
            closed_par += 1
        elif s[i] == "," and opened_par < closed_par + 2:
            lst.append(Formula.parse_prefix_SAME(s[last_comma + 1:i])[0])
            last_comma = i
        i += 1
    if last_comma + 1 != i - 1:
        lst.append(Formula.parse_prefix_SAME(s[last_comma + 1:i - 1])[0])
    if is_relation(s[0]):
        this_formula = Formula(name, lst)
        return [this_formula, s[i:]]
    else:
        this_term = Term(name, lst)
        return [this_term, s[i:]]


def constant_or_variable(s):
    i, j = 1, 0
    if len(s) > 1:
        while (is_constant(s[j:i]) or is_variable((s[j:i]))) and i < len(s):
            if is_equality(s[i]) or s[i] == ']':
                j = 1
            i += 1
        if i == len(s):
            return [(Term(s[0:i - j])), s[i:]]
        return [(Term(s[0:i - j])), s[i - 1:]]
    return [(Term(s)), ""]


def binary(s):
    sign, first = None, None
    i, mid, r_counter, l_counter = 0, 0, 0, 0
    while not (l_counter == r_counter != 0) and i < len(s):
        if s[i] == '(':
            l_counter += 1
        elif s[i] == ')':
            r_counter += 1
        elif is_binary(s[i]) and l_counter - r_counter == 1:
            first = Formula.parse_prefix(s[l_counter - r_counter:i])
            mid, sign = i, s[i]
        elif is_binary(s[i:i + 2]) and l_counter - r_counter == 1:
            first = Formula.parse_prefix(s[l_counter - r_counter:i])
            mid, sign = i + 1, s[i:i + 2]
        i += 1
    second = Formula.parse_prefix(s[mid + 1:i - 1])
    if mid == 0:
        return second
    if first[1] != '' and first[1][0] == EQU:
        first[0] = Formula(EQU, first[0], Formula.parse_prefix(first[1][1:])[0])
    if second[1] != '' and second[1][0] == EQU:
        second = [Formula(EQU, second[0], Formula.parse_prefix(second[1][1:])[0]), '']
    return [Formula(sign, first[0], second[0]), second[1] + s[i:]]


def binary_SAME(s):
    sign, first = None, None
    i, mid, r_counter, l_counter = 0, 0, 0, 0
    while not (l_counter == r_counter != 0) and i < len(s):
        if s[i] == '(':
            l_counter += 1
        elif s[i] == ')':
            r_counter += 1
        elif is_binary(s[i]) and l_counter - r_counter == 1:
            first = Formula.parse_prefix(s[l_counter - r_counter:i])
            mid, sign = i, s[i]
        elif is_binary(s[i:i + 2]) and l_counter - r_counter == 1:
            first = Formula.parse_prefix(s[l_counter - r_counter:i])
            mid, sign = i + 1, s[i:i + 2]
        i += 1
    second = Formula.parse_prefix_SAME(s[mid + 1:i - 1])
    if first[1] != '' and first[1][0] == EQU:
        first[0] = Formula(SAME, [first[0], Formula.parse_prefix_SAME(first[1][1:])[0]])
    if second[1] != '' and second[1][0] == EQU:
        second = [Formula(SAME, [second[0], Formula.parse_prefix_SAME(second[1][1:])[0]]), '']
    return [Formula(sign, first[0], second[0]), second[1] + s[i:]]


class Formula:
    """ A Formula in first-order logic """

    def __init__(self, root, first=None, second=None):
        if is_relation(root):  # Populate self.root and self.arguments
            assert second is None
            for x in first:
                assert type(x) is Term
            self.root, self.arguments = root, first
        elif is_equality(root):  # Populate self.first and self.second
            assert type(first) is Term and type(second) is Term
            self.root, self.first, self.second = root, first, second
        elif is_quantifier(root):  # Populate self.variable and self.predicate
            assert is_variable(first) and type(second) is Formula
            self.root, self.variable, self.predicate = root, first, second
        elif is_unary(root):  # Populate self.first
            assert type(first) is Formula and second is None
            self.root, self.first = root, first
        else:  # Populate self.first and self.second
            assert is_binary(root) and type(first) is Formula and type(second) is Formula
            self.root, self.first, self.second = root, first, second

    def __repr__(self):
        """ Return the usual (infix for operators and equality, functional for
            other relations) representation of self """
        return self.infix()

    def __eq__(self, other):
        return str(self) == str(other)

    def __ne__(self, other):
        return not self == other

    def __hash__(self):
        return hash(str(self))

    def infix(self):
        """ Return an infix representation of self """

        if is_constant(self.root) or is_variable(self.root):
            return self.root
        elif is_function(self.root):
            args = self.arguments[0].infix()
            for i in self.arguments[1:]:
                args = args + ',' + i.infix()
            return self.root + '(' + args + ')'
        elif is_equality(self.root):
            return self.first.infix() + EQU + self.second.infix()
        elif is_quantifier(self.root):
            return self.root + self.variable + '[' + self.predicate.infix() + ']'
        elif is_relation(self.root):
            args = ''
            if self.arguments:
                args = self.arguments[0].infix()
                for i in self.arguments[1:]:
                    args = args + ',' + i.infix()
            return self.root + '(' + args + ')'
        elif is_unary(self.root):
            return self.root + self.first.infix()
        elif is_binary(self.root):
            return "(" + self.first.infix() + self.root + self.second.infix() + ")"

    @staticmethod
    def parse_prefix(s):
        """ Parse a first-order formula from the prefix of a given string.
            Return a pair: the parsed formula, and unparsed remainder of the
            string """
        # Task 7.4.1
        if s[0] == '(':
            return binary(s)
        elif is_constant(s[0]) or is_variable(s[0]):
            return constant_or_variable(s)
        elif is_function(s[0]) or is_relation(s[0]):
            return function_or_relation(s)
        elif is_quantifier(s[0]):
            return quantifier(s)
        elif is_unary(s[0]):
            return unary(s)

    @staticmethod
    def parse_prefix_SAME(s):
        """ Parse a first-order formula from the prefix of a given string.
            Return a pair: the parsed formula, and unparsed remainder of the
            string """
        # Task 7.4.1
        if s[0] == '(':
            return binary_SAME(s)
        elif is_constant(s[0]) or is_variable(s[0]):
            return constant_or_variable(s)
        elif is_function(s[0]) or is_relation(s[0]):
            return function_or_relation_SAME(s)
        elif is_quantifier(s[0]):
            return quantifier_SAME(s)
        elif is_unary(s[0]):
            return unary_SAME(s)

    @staticmethod
    def parse(s):
        """ Return a first-order formula parsed from its given string
            representation """
        # Task 7.4.2
        res, s = Formula.parse_prefix(s)
        while s != '':
            if s[0] == "=":
                x, s = Formula.parse_prefix(s[1:])
                res = Formula('=', res, x)
        return res

    # (((Ax[(Man(x)->Ex[Mortal(x)])]&Ex[Man(x)])->Ex[Mortal(x)])->Ex[Mortal(x)])
    @staticmethod
    def parse_with_SAME(s):
        """ Return a first-order formula parsed from its given string
            representation """
        # Task 7.4.2
        res, s = Formula.parse_prefix_SAME(s)
        while s != '':
            if s[0] == "=":
                x, s = Formula.parse_prefix_SAME(s[1:])
                res = Formula('SAME', [res, x])
        return res

    def free_variables(self):
        """ Return the set of variables that are free in this formula """
        # Task 7.6
        ret = set()
        if is_variable(self.root):
            return {self.root}
        elif is_term(self.root):
            return self.root.variables()
        elif is_relation(self.root):
            for arg in self.arguments:
                ret = ret | arg.variables()
            return ret
        elif is_equality(self.root):
            return self.first.variables() | self.second.variables()
        elif is_unary(self.root):
            return self.first.free_variables()
        elif is_binary(self.root):
            return self.first.free_variables() | self.second.free_variables()
        elif is_quantifier(self.root):
            ret = self.predicate.free_variables()
            if self.variable in ret:
                ret.remove(self.variable)
            return ret

    def functions(self):
        """ Return a set of pairs (function_name, arity) for all function names
            that appear in this formula """
        # Task 8.1.2
        ret = set()
        if is_function(self.root[0]):
            arity = len(self.arguments)
            ret.add((self.root, arity))
            for arg in self.arguments:
                ret = ret | arg.functions()
        elif is_equality(self.root):
            ret = self.first.functions() | self.second.functions()
        elif is_relation(self.root[0]):
            for arg in self.arguments:
                ret = ret | arg.functions()
        elif is_binary(self.root):
            ret = self.first.functions() | self.second.functions()
        elif is_unary(self.root):
            ret = self.first.functions()
        elif is_quantifier(self.root):
            ret = self.predicate.functions()
        return ret

    def relations(self):
        """ Return a set of pairs (relation_name, arity) for all relation names
            that appear in this formula """
        # Task 8.1.3
        ret = set()
        if is_relation(self.root[0]):
            arity = len(self.arguments)
            ret.add((self.root, arity))
            for arg in self.arguments:
                ret = ret | arg.relations()
        elif is_equality(self.root):
            ret = self.first.relations() | self.second.relations()
        elif is_function(self.root[0]):
            for arg in self.arguments:
                ret = ret | arg.relations()
        elif is_binary(self.root):
            ret = self.first.relations() | self.second.relations()
        elif is_unary(self.root):
            ret = self.first.relations()
        elif is_quantifier(self.root):
            ret = self.predicate.relations()
        return ret

    def substitute(self, substitution_map):
        """ Return a first-order formula obtained from this formula where all
            occurrences of each constant name element_name and all *free*
            occurrences of each variable name element_name for element_name
            that appears as a key in the dictionary substitution_map are
            replaced with substitution_map[element_name] """
        for element_name in substitution_map:
            assert (is_constant(element_name) or is_variable(element_name)) and \
                   type(substitution_map[element_name]) is Term
        # Task 9.2
        new_func = copy.deepcopy(self)
        if is_term(new_func.root):
            return new_func.substitute(substitution_map)
        elif is_quantifier(new_func.root):
            new_map = substitution_map
            if new_func.variable in substitution_map:
                x = new_map.pop(new_func.variable, None)
                new_func.predicate = new_func.predicate.substitute(new_map)
                new_map[new_func.variable] = x
            else:
                new_func.predicate = new_func.predicate.substitute(new_map)
            return new_func
        elif is_unary(new_func.root):
            new_func.first = new_func.first.substitute(substitution_map)
        elif is_relation(new_func.root):
            for i, term in enumerate(new_func.arguments):
                new_func.arguments[i] = term.substitute(substitution_map)
        elif is_equality(new_func.root) or is_binary(new_func.root):
            new_func.first = new_func.first.substitute(substitution_map)
            new_func.second = new_func.second.substitute(substitution_map)
        return new_func

    def propositional_skeleton(self):
        """ Return a PropositionalFormula that is the skeleton of this one.
            The variables in the propositional formula will have the names
            z1,z2,... (obtained by calling next(fresh_variable_name_generator)),
            starting from left to right """
        # Task 9.5
        return self.propositional_skeleton_helper(dict())

    def propositional_skeleton_helper(self, switches_dict):
        if is_unary(self.root):
            return PropositionalFormula(self.root, self.first.propositional_skeleton_helper(switches_dict))
        if is_binary(self.root):
            return PropositionalFormula(self.root, self.first.propositional_skeleton_helper(switches_dict),
                                        self.second.propositional_skeleton_helper(switches_dict))
        if self in switches_dict:
            return switches_dict[self]
        else:
            value = PropositionalFormula(next(fresh_variable_name_generator))
            switches_dict[self] = value
            return value

    def variables(self):
        return self.free_variables()
