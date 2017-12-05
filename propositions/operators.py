""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/operators.py """

from propositions.syntax import *
from propositions.semantics import *


def to_not_and_or(formula):
    """ Return an equivalent formula that has no operators beyond not, and, and
        or """
    try:
        formula.first = to_not_and_or(formula.first)
        try:
            formula.second = to_not_and_or(formula.second)
        except AttributeError:
            return formula
        if formula.root == AND or formula.root == OR:
            return (Formula(formula.root, to_not_and_or(formula.first),
                            to_not_and_or(formula.second)))
        elif formula.root == IMP:
            return (Formula(OR, Formula(NOT, to_not_and_or(formula.first)),
                            to_not_and_or(formula.second)))
        elif formula.root == IFF:
            a = Formula(AND, to_not_and_or(formula.first),
                        to_not_and_or(formula.second))
            b = Formula(OR, to_not_and_or(formula.first),
                        to_not_and_or(formula.second))
            return Formula(OR, a, Formula(NOT, b))
        elif formula.root == NOR:
            return (Formula(NOT, Formula(OR, to_not_and_or(formula.first),
                                         to_not_and_or(formula.second))))
        elif formula.root == NAND:
            return (Formula(NOT, Formula(AND, to_not_and_or(formula.first),
                                         to_not_and_or(formula.second))))
        elif formula.root == MUX:
            formula.third = to_not_and_or(formula.third)
            a = Formula(OR, Formula(NOT, to_not_and_or(formula.first)),
                        to_not_and_or(formula.second))
            b = Formula(OR, to_not_and_or(formula.first),
                        to_not_and_or(formula.third))
            return Formula(AND, a, b)
    except AttributeError:
        return formula


def to_not_and(formula):
    """ Return an equivalent formula that has no operators beyond not and and,
        and has no constants """
    try:
        formula.first = to_not_and(formula.first)
        try:
            formula.second = to_not_and(formula.second)
        except AttributeError:
            return formula
        if formula.root == AND:
            return formula
        elif formula.root == OR:
            return make_or_from_not_and(formula.first, formula.second)

        elif formula.root == IMP:
            return make_or_from_not_and(
                Formula(NOT, to_not_and(formula.first)),
                to_not_and(formula.second))
        elif formula.root == IFF:
            a = Formula(AND, to_not_and(formula.first),
                        to_not_and(formula.second))
            b = make_or_from_not_and(to_not_and(formula.first),
                                     to_not_and(formula.second))
            return make_or_from_not_and(a, Formula(NOT, b))
        elif formula.root == NOR:
            return Formula(NOT, make_or_from_not_and(to_not_and(formula.first),
                                                     to_not_and(
                                                         formula.second)))
        elif formula.root == NAND:
            return (Formula(NOT, Formula(AND, to_not_and(formula.first),
                                         to_not_and(formula.second))))
        elif formula.root == MUX:
            formula.third = to_not_and(formula.third)
            a = make_or_from_not_and(Formula(NOT, to_not_and(formula.first)),
                                     to_not_and(formula.second))
            b = make_or_from_not_and(to_not_and(formula.first),
                                     to_not_and(formula.third))
            return Formula(AND, a, b)
    except AttributeError:
        return formula


def make_or_from_not_and(first, second):
    return Formula(NOT, Formula(AND, Formula(NOT, to_not_and(first)),
                                Formula(NOT, to_not_and(second))))


def synthesize_not_and(models, values):
    """ Return a propositional formula that has the given list of respective
        truth values in the given list of models, has no operators beyond not
        and and, and has no constants """
    return to_not_and(synthesize(models, values))


def to_implies_false(formula):
    """ Return an equivalent formula that has no operators beyond implies, and
        has no constants beyond false """
    try:
        formula.first = to_implies_false(formula.first)
        if formula.root == NOT:
            return make_not_from_imp_false(formula.first)
        try:
            formula.second = to_implies_false(formula.second)
        except AttributeError:
            return formula

        if formula.root == AND:
            return make_and_from_imp_false(formula.first, formula.second)

        elif formula.root == OR:
            return make_or_from_imp_false(formula.first, formula.second)

        elif formula.root == IMP:
            return formula

        elif formula.root == IFF:
            return make_and_from_imp_false(
                Formula(IMP, formula.first, formula.second),
                Formula(IMP, formula.second, formula.first))

        elif formula.root == NOR:
            x = Formula(NOT, make_or_from_not_and(to_not_and(formula.first),
                                                  to_not_and(formula.second)))
            return to_implies_false(x)
        elif formula.root == NAND:
            return Formula(IMP, formula.first, make_not_from_imp_false(
                formula.second))
        elif formula.root == MUX:
            formula.third = to_not_and_or(formula.third)
            a = Formula(OR, Formula(NOT, to_not_and_or(formula.first)),
                        to_not_and_or(formula.second))
            b = Formula(OR, to_not_and_or(formula.first),
                        to_not_and_or(formula.third))
            x = (Formula(AND, a, b))
            return to_implies_false(x)
    except AttributeError:
        return formula


def make_not_from_imp_false(formula):
    return Formula(IMP, formula, Formula(FALSE))


def make_and_from_imp_false(first, second):
    v = Formula(IMP, first, second)
    y = make_not_from_imp_false(v)
    x = Formula(IMP, first, y)
    return make_not_from_imp_false(x)


def make_or_from_imp_false(first, second):
    v = make_not_from_imp_false(second)
    y = make_not_from_imp_false(first)
    x = make_and_from_imp_false(y, v)
    return make_not_from_imp_false(x)


def synthesize_implies_false(models, values):
    """ Return a propositional formula that has the given list of respective
        truth values in the given list of models, has no operators beyond
        implies, and has no constants beyond false """
    return to_implies_false(synthesize(models, values))


def to_nand(formula):
    """ Return an equivalent formula that has no operators beyond nand, and has
        no constants """
    try:
        formula.first = to_nand(formula.first)
        if formula.root == NOT:
            return Formula(NAND, to_nand(formula.first),
                           to_nand(formula.first))
        try:
            formula.second = to_nand(formula.second)
        except AttributeError:
            return formula

        if formula.root == AND:
            x = Formula(NAND, to_nand(formula.first), to_nand(formula.second))
            return Formula(NAND, x, x)

        elif formula.root == OR:
            x = Formula(NAND, to_nand(formula.first), to_nand(formula.first))
            y = Formula(NAND, to_nand(formula.second), to_nand(formula.second))
            return Formula(NAND, x, y)

        elif formula.root == IMP:
            y = Formula(NAND, to_nand(formula.second), to_nand(formula.second))
            return Formula(NAND, formula.first, y)

        elif formula.root == IFF:
            x = Formula(NAND, to_nand(formula.first), to_nand(formula.first))
            y = Formula(NAND, to_nand(formula.second), to_nand(formula.second))
            z = Formula(NAND, x, y)
            t = Formula(NAND, to_nand(formula.first), to_nand(formula.second))
            return Formula(NAND, z, t)

        elif formula.root == NOR:
            x = Formula(NAND, to_nand(formula.first), to_nand(formula.first))
            y = Formula(NAND, to_nand(formula.second), to_nand(formula.second))
            z = Formula(NAND, x, y)
            return Formula(NAND, z, z)

        elif formula.root == NAND:
            return formula

        elif formula.root == MUX:
            sel = to_nand(formula.first)
            n_sel = Formula(NAND, sel, sel)
            x = Formula(NAND, to_nand(formula.third), n_sel)
            y = Formula(NAND, to_nand(formula.second), sel)
            return Formula(NAND, x, y)

    except AttributeError:
        return formula


def synthesize_nand(models, values):
    """ Return a propositional formula that has the given list of respective
        truth values in the given list of models, has no operators beyond nand,
        and has no constants """

    return to_nand(synthesize(models, values))


def to_nor(formula):
    """ Return an equivalent formula that has no operators beyond nor, and has
        no constants """
    try:
        formula.first = to_nor(formula.first)
        if formula.root == NOT:
            return Formula(NOR, to_nor(formula.first),
                           to_nor(formula.first))
        try:
            formula.second = to_nor(formula.second)
        except AttributeError:
            return formula

        if formula.root == AND:
            x = Formula(NOR, to_nor(formula.first), to_nor(formula.first))
            y = Formula(NOR, to_nor(formula.second), to_nor(formula.second))
            return Formula(NOR, x, y)

        elif formula.root == OR:
            x = Formula(NOR, to_nor(formula.first), to_nor(formula.second))
            return Formula(NOR, x, x)

        elif formula.root == IMP:
            x = Formula(NOR, to_nor(formula.first), to_nor(formula.second))
            y = Formula(NOR, to_nor(formula.second), x)
            return Formula(NOR, y, y)

        elif formula.root == IFF:
            x = Formula(NOR, to_nor(formula.first), to_nor(formula.second))
            y = Formula(NOR, to_nor(formula.first), x)
            z = Formula(NOR, to_nor(formula.second), x)

            return Formula(NOR, y, z)

        elif formula.root == NOR:
            return formula

        elif formula.root == NAND:
            x = Formula(NOR, to_nor(formula.first), to_nor(formula.first))
            y = Formula(NOR, to_nor(formula.second), to_nor(formula.second))
            z = Formula(NOR, x, y)
            return Formula(NOR, z, z)

        elif formula.root == MUX:
            sel = to_nor(formula.first)
            n_sel = Formula(NOR, sel, sel)
            x = Formula(NOR, to_nor(formula.third), sel)
            y = Formula(NOR, to_nor(formula.second), n_sel)
            return Formula(NOR, x, y)

    except AttributeError:
        return formula


def synthesize_nor(models, values):
    """ Return a propositional formula that has the given list of respective
        truth values in the given list of models, has no operators beyond nor,
        and has no constants """
    return to_nor(synthesize(models, values))


def to_mux(formula):
    """ Return an equivalent formula that has no operators beyond mux """
    t = Formula(TRUE)
    f = Formula(FALSE)
    try:
        formula.first = to_mux(formula.first)
        if formula.root == NOT:
            return Formula(MUX, to_mux(formula.first), f, t)
        try:
            formula.second = to_mux(formula.second)
        except AttributeError:
            return formula

        if formula.root == AND:
            return Formula(MUX, to_mux(formula.second), to_mux(formula.first),
                           f)

        elif formula.root == OR:
            return Formula(MUX, to_mux(formula.second), t,
                           to_mux(formula.first))

        elif formula.root == IMP:
            return Formula(MUX, to_mux(formula.first),
                           to_mux(formula.second), t)

        elif formula.root == IFF:
            not_first = Formula(MUX, to_mux(formula.first), f, t)
            return Formula(MUX, to_mux(formula.second), to_mux(formula.first),
                           not_first)
        elif formula.root == NOR:
            not_first = Formula(MUX, to_mux(formula.first), f, t)
            return Formula(MUX, to_mux(formula.second), f, not_first)

        elif formula.root == NAND:
            not_first = Formula(MUX, to_mux(formula.first), f, t)
            return Formula(MUX, to_mux(formula.second), not_first, t)

        elif formula.root == MUX:
            return Formula(MUX, formula.first, formula.second, formula.third)
    except AttributeError:
        return formula


def synthesize_mux(models, values):
    """ Return a propositional formula that has the given list of respective
        truth values in the given list of models, has no operators beyond
        mux """
    return to_mux(synthesize(models, values))
