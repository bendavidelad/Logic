""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/syntax.py """

from propositions.syntax import Formula as PropositionalFormula
from predicates.util import *

def is_unary(s):
    """ Is s a unary operator? """
    return s == '~'

def is_binary(s):
    """ Is s a binary boolean operator? """
    return s == '&' or s == '|' or s == '->'

def is_equality(s):
    """ Is s the equality relation? """
    return s == "="

def is_quantifier(s):
    """ Is s a quantifier? """
    return s == "A" or s == "E"

def is_relation(s):
    """ Is s a relation name? """
    return s[0] >= 'F' and s[0] <= 'T' and s.isalnum()

def is_constant(s):
    """ Is s a constant name? """
    return  ((s[0] >= '0' and s[0] <= '9') or (s[0] >= 'a' and s[0] <= 'd')) and s.isalnum()

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

    def __eq__(self, other):
        return str(self) == str(other)
        
    def __ne__(self, other):
        return not self == other

    def __hash__(self):
        return hash(str(self))

    @staticmethod
    def parse_prefix(s):
        """ Parse a term from the prefix of a given string. Return a pair: the
            parsed term, and the unparsed remainder of the string """
        # Task 7.3.1

    @staticmethod
    def parse(s):
        """ Return a term parsed from its given string representation """
        # Task 7.3.2

    def variables(self):
        """ Return the set of variables in this term """
        # Task 7.5

    def functions(self):
        """ Return a set of pairs (function_name, arity) for all function names
            that appear in this term """
        # Task 8.1.1
    
    def substitute_variables(self, substitution_map):
        """ Return a term obtained from this term where all the occurrences of
            each variable v that appears in the dictionary substitution_map are
            replaced with the term substitution_map[v] """
        for variable in substitution_map:
            assert is_variable(variable) and \
                   type(substitution_map[variable]) is Term
        # Task 9.1

    def substitute_constants(self, substitution_map):
        """ Return a term obtained from this formula where all the occurrences
            of each constant c that appears in the dictionary substitution_map
            are replaced with the term substitution_map[v] """
        for constant in substitution_map:
            assert is_constant(constant) and \
                   type(substitution_map[constant]) is Term
        # Ex12


class Formula:
    """ A Formula in first-order logic """
    
    def __init__(self, root, first=None, second=None):
        if is_relation(root): # Populate self.root and self.arguments
            assert second is None
            for x in first:
                assert type(x) is Term
            self.root, self.arguments = root, first
        elif is_equality(root): # Populate self.first and self.second
            assert type(first) is Term and type(second) is Term
            self.root, self.first, self.second = root, first, second
        elif is_quantifier(root): # Populate self.variable and self.predicate
            assert is_variable(first) and type(second) is Formula
            self.root, self.variable, self.predicate = root, first, second
        elif is_unary(root): # Populate self.first
            assert type(first) is Formula and second is None
            self.root, self.first = root, first
        else: # Populate self.first and self.second
            assert is_binary(root) and type(first) is Formula and type(second) is Formula
            self.root, self.first, self.second = root, first, second           

    def __repr__(self):
        """ Return the usual (infix for operators and equality, functional for
            other relations) representation of self """
        # Task 7.2

    def __eq__(self, other):
        return str(self) == str(other)
        
    def __ne__(self, other):
        return not self == other

    def __hash__(self):
        return hash(str(self))

    @staticmethod
    def parse_prefix(s):
        """ Parse a first-order formula from the prefix of a given string.
            Return a pair: the parsed formula, and unparsed remainder of the
            string """
        # Task 7.4.1

    @staticmethod
    def parse(s):
        """ Return a first-order formula parsed from its given string
            representation """
        # Task 7.4.2

    def free_variables(self):
        """ Return the set of variables that are free in this formula """
        # Task 7.6

    def functions(self):
        """ Return a set of pairs (function_name, arity) for all function names
            that appear in this formula """
        # Task 8.1.2

    def relations(self):
        """ Return a set of pairs (relation_name, arity) for all relation names
            that appear in this formula """
        # Task 8.1.3

    def substitute_variables(self, substitution_map):
        """ Return a first-order formula obtained from this formula where all
            the free occurrences of each variable v that appears in the
            dictionary substitution_map are replaced with the term
            substitution_map[v] """
        for variable in substitution_map:
            assert is_variable(variable) and \
                   type(substitution_map[variable]) is Term
        # Task 9.2

    def substitute_constants(self, substitution_map):
        """ Return a first-order formula obtained from this formula where all
            the occurrences of each constant c that appears in the dictionary
            substitution_map are replaced with the term substitution_map[v] """
        for constant in substitution_map:
            assert is_constant(constant) and \
                   type(substitution_map[constant]) is Term
        # Ex12

    def propositional_skeleton(self):
        """ Return a PropositionalFormula that is the skeleton of this one.
            The variables in the propositional formula will have the names
            z1,z2,... (obtained by calling next(fresh_variable_name_generator)),
            starting from left to right """
        # Task 9.5
