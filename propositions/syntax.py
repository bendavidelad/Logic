""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/syntax.py """


def is_variable(s):
    """ Is s an atomic proposition?  """
    return s[0] >= 'p' and s[0] <= 'z' and (len(s) == 1 or s[1:].isdigit())


def is_unary(s):
    """ Is s a unary operator? """
    return s == '~'


def is_binary(s):
    """ Is s a binary operator? """
    return s == '&' or s == '|' or s == '->' or s == '<->' or s == '-&' or s == '-|'


def is_ternary(s):
    """ Is s a ternary operator? """
    return s == '?:'


def is_constant(s):
    """ Is s a constant? """
    return s == 'T' or s == 'F'


class Formula:
    """ A Propositional Formula """

    def __init__(self, root, first=None, second=None, third=None):
        """ Create a new formula from its root (a string) and, when needed, the
        first and second operands (each of them a Formula)."""
        if is_constant(root) or is_variable(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            assert type(first) is Formula and second is None
            self.root, self.first = root, first
        elif is_binary(root):
            assert is_binary(root) and type(first) is Formula and type(second) is Formula
            self.root, self.first, self.second = root, first, second
        else:
            self.root, self.first, self.second, self.third = root, first, second, third

    def __repr__(self):
        return self.infix()

    def __eq__(self, other):
        return self.infix() == other.infix()

    def __ne__(self, other):
        return not self == other

    def infix(self):
        """ Return an infix representation of self """
        if is_constant(self.root) or is_variable(self.root):
            return self.root
        elif is_unary(self.root):
            return self.root + self.first.infix()
        elif is_binary(self.root):
            return "(" + self.first.infix() + self.root + self.second.infix() + ")"
        else:
            return "(" + self.first.infix() + "?" + self.second.infix() + ":" + self.third.infix() + ")"

    @staticmethod
    def from_infix(s):
        """ Return a propositional formula whose infix representation is s """
        if s[0] == '~':
            return Formula('~', Formula.from_infix(s[1:]))
        elif s[0] == '(':
            parenthesis_counter = 0
            for letter in range(1, len(s), 1):
                if s[letter] == "(":
                    parenthesis_counter += 1
                elif s[letter] == ")":
                    parenthesis_counter -= 1
                elif s[letter] == '&' or s[letter] == '|':
                    if parenthesis_counter == 0:
                        return Formula(s[letter], Formula.from_infix(s[1:letter]),
                                       Formula.from_infix((s[letter + 1:-1])))
                elif s[letter] == '-':
                    if parenthesis_counter == 0:
                        return Formula(s[letter:letter + 2], Formula.from_infix(s[1:letter]),
                                       Formula.from_infix((s[letter + 2:-1])))
                elif s[letter] == '<':
                    if parenthesis_counter == 0:
                        return Formula(s[letter:letter + 3], Formula.from_infix(s[1:letter]),
                                       Formula.from_infix((s[letter + 3:-1])))
                elif s[letter] == '?':
                    if parenthesis_counter == 0:
                        second_parenthesis_counter = 0
                        colon = letter
                        while colon < len(s):
                            if s[colon] == ":":
                                if second_parenthesis_counter == 0:
                                    break
                            elif s[colon] == "(":
                                second_parenthesis_counter += 1
                            elif s[colon] == ")":
                                second_parenthesis_counter -= 1
                            colon += 1
                        return Formula(s[letter] + s[colon], Formula.from_infix(s[1:letter]),
                                       Formula.from_infix(s[letter + 1:colon]),
                                       Formula.from_infix(s[colon + 1: -1]))
        else:
            return Formula(s)

    def prefix(self):
        """ Return a prefix representation of self """
        if is_constant(self.root) or is_variable(self.root):
            return self.root
        elif is_unary(self.root):
            return self.root + self.first.prefix()
        elif is_binary(self.root):
            return self.root + self.first.prefix() + self.second.prefix()
        else:
            return self.root + self.first.prefix() + self.second.prefix() + self.third.prefix()

    @staticmethod
    def from_prefix(s):
        """ Return a propositional formula whose prefix representation is s """
        if s[0] == '~':
            return Formula('~', Formula.from_prefix(s[1:]))
        elif s[0] == '&' or s[0] == "|" or s[0] == '-' or s[0] == '<' or s[0] == '?':
            counter = 1
            if s[0] == '-' or s[0] == '?':
                letter = 2
            elif s[0] == '<':
                letter = 3
            else:
                letter = 1
            while counter > 0:
                if s[letter] == 'F' or s[letter] == 'T':
                    counter -= 1
                elif 'p' <= s[letter] <= 'z':
                    while s[letter + 1].isdigit():
                        letter += 1
                    counter -= 1
                elif s[letter] == '&' or s[letter] == '|':
                    counter += 1
                elif s[letter] == '-':
                    counter += 1
                    letter += 1
                elif s[letter] == '<':
                    counter += 1
                    letter += 2
                elif s[letter] == '?':
                    counter += 2
                    letter += 1
                letter += 1
            if s[0] == '-':
                return Formula(s[0:2], Formula.from_prefix(s[2:letter]), Formula.from_prefix(s[letter:]))
            elif s[0] == '<':
                return Formula(s[0:3], Formula.from_prefix(s[3:letter]), Formula.from_prefix(s[letter:]))
            elif s[0] == '?':
                second_counter = 1
                second_letter = letter
                while second_counter > 0:
                    if s[second_letter] == 'F' or s[second_letter] == 'T':
                        second_counter -= 1
                        second_letter += 1
                    elif 'p' <= s[second_letter] <= 'z':
                        while s[second_letter + 1].isdigit():
                            second_letter += 1
                        second_counter -= 1
                        second_letter += 1
                    elif s[second_letter] == '&' or s[second_letter] == '|':
                        second_counter += 1
                    elif s[second_letter] == '-':
                        second_counter += 1
                        second_letter += 2
                    elif s[second_letter] == '<':
                        second_counter += 1
                        second_letter += 3
                    elif s[second_letter] == '?':
                        second_counter += 2
                        second_letter += 2
                return Formula(s[0:2], Formula.from_prefix(s[2:letter]),
                               Formula.from_prefix(s[letter:second_letter]),
                               Formula.from_prefix(s[second_letter:]))
            else:
                return Formula(s[0:1], Formula.from_prefix(s[1:letter]), Formula.from_prefix(s[letter:]))
        else:
            return Formula(s)

    def variables(self):
        """ Return the set of atomic propositions (variables) used in self """
        if is_constant(self.root) or is_variable(self.root):
            if self.root == 'T' or self.root == 'F':
                return set()
            else:
                return {self.root}
        elif is_unary(self.root):
            return self.first.variables()
        elif is_binary(self.root):
            return self.first.variables() | self.second.variables()
        else:
            return self.first.variables() | self.second.variables() | self.third.variables()
