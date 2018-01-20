""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/completeness.py """

from predicates.syntax import *
from predicates.semantics import *
from predicates.proofs import *
from predicates.prover import *
from predicates.prenex import *
from predicates.util import *
from itertools import product
from predicates.deduction import *


def is_closed(sentences, constants):
    """ Return whether the given set of sentences closed with respect to the
        given set of constant names """
    for sentence in sentences:
        assert type(sentence) is Formula and is_in_prenex_normal_form(sentence)
    for constant in constants:
        assert is_constant(constant)
    return is_primitively_closed(sentences, constants) and \
           is_universally_closed(sentences, constants) and \
           is_existentially_closed(sentences, constants)


def is_primitively_closed(sentences, constants):
    """ Return whether the given set of prenex-normal-form sentences is
        primitively closed with respect to the given set of constant names """
    # Task 12.1.1
    for constant in constants:
        assert is_constant(constant)
    used_set = set()
    for sentence in sentences:
        assert type(sentence) is Formula and is_in_prenex_normal_form(sentence)
        for g in sentence.relations():
            if g[0] not in used_set:
                used_set.add(g[0])
                for names in list(product(constants, repeat=g[1])):
                    check = Formula(g[0], [Term(i) for i in names])
                    if check not in sentences and Formula('~', check) not in sentences:
                        return False
    return True


def is_universally_closed(sentences, constants):
    """ Return whether the given set of prenex-normal-form sentences is
        universally closed with respect to the given set of constant names """
    # Task 12.1.2
    for constant in constants:
        assert is_constant(constant)
    for sentence in sentences:
        assert type(sentence) is Formula and is_in_prenex_normal_form(sentence)
        if sentence.root == "A":
            for con in constants:
                if sentence.predicate.substitute({sentence.variable: Term(con)}) not in sentences:
                    return False
    return True


def is_existentially_closed(sentences, constants):
    """ Return whether the given set of prenex-normal-form sentences is
        existentially closed with respect to the given set of constant names """
    # Task 12.1.3
    for constant in constants:
        assert is_constant(constant)
    for sentence in sentences:
        assert type(sentence) is Formula and is_in_prenex_normal_form(sentence)
        if sentence.root == "E":
            check = False
            for con in constants:
                if sentence.predicate.substitute({sentence.variable: Term(con)}) in sentences:
                    check = True
            if not check:
                return check
    return True


def find_unsatisfied_quantifier_free_sentence(sentences, constants, model, unsatisfied):
    """ Given a set of prenex-normal-form sentences that is closed with respect
        to the given set of constants names, given a model whose universe is
        the given set of constant names, and given a sentence (which possibly
        contains quantifiers) from the given set that the given model does not
        satisfy, return a quantifier-free sentence from the given set that the
        given model does not satisfy. The set sentences may only be accessed
        using containment queries, i.e., using the "in" operator as in:
        if sentence in sentences """
    for constant in constants:
        assert is_constant(constant)
    assert type(model) is Model
    assert model.universe == constants
    assert type(unsatisfied) is Formula
    assert unsatisfied in sentences
    assert not model.evaluate_formula(unsatisfied)
    # Task 12.2
    if unsatisfied.root == "A":
        for con in constants:
            x = unsatisfied.predicate.substitute({unsatisfied.variable: Term(con)})
            if not model.evaluate_formula(x):
                return find_unsatisfied_quantifier_free_sentence(sentences, constants, model, x)
    elif unsatisfied.root == "E":
        for con in constants:
            x = unsatisfied.predicate.substitute({unsatisfied.variable: Term(con)})
            if x in sentences:
                return find_unsatisfied_quantifier_free_sentence(sentences, constants, model, x)
    return unsatisfied


def get_primitives(quantifier_free):
    """ Return a set containing the primitive formulae (i.e., relation
        instantiations) that appear in the given quantifier-free formula. For
        example, if quantifier_free is '(R(c1,d)|~(Q(c1)->~R(c2,a))', then the
        returned set should be {'R(c1,d)', 'Q(c1)', 'R(c2,a)'} """
    assert type(quantifier_free) is Formula and is_quantifier_free(quantifier_free)
    # Task 12.3.1
    if is_relation(quantifier_free.root):
        return {quantifier_free}
    elif is_binary(quantifier_free.root):
        return get_primitives(quantifier_free.first) | get_primitives(quantifier_free.second)
    elif is_unary(quantifier_free.root):
        return get_primitives(quantifier_free.first)


def model_or_inconsistent(sentences, constants):
    """ Given a set of prenex-normal-form sentences that is closed with respect
        to the given set of constants names, return either a model for the
        given set of sentences, or a proof of a contradiction from these
        sentences as assumptions """
    assert is_closed(sentences, constants)
    # Task 12.3.2
    meaning = dict()
    for sen in sentences:
        if is_relation(sen.root):
            if sen.root in meaning.keys():
                meaning[sen.root].add(tuple(sen.arguments))
            else:
                meaning[sen.root] = {tuple(sen.arguments)}
    for con in constants:
        meaning[con] = con
    model = Model(constants, meaning)
    for sen2 in sentences:
        if not model.evaluate_formula(sen2):
            quantifier_free = find_unsatisfied_quantifier_free_sentence(sentences, constants, model, sen2)
            return prove_contradiction(quantifier_free, sentences)
    return model


def prove_contradiction(quantifier_free, sentences):
    primitives = get_primitives(quantifier_free)
    for x in primitives:
        if x not in sentences:
            primitives.remove(x)
            primitives.add(Formula('~', x))
    quantifier_free_n = Formula('~', quantifier_free)
    goal = Formula('&', quantifier_free, quantifier_free_n).infix()
    prover = Prover([Schema(x.infix()) for x in sentences], goal)
    for i in primitives:
        prover.add_assumption(i)
    step1 = prover.add_tautological_inference(quantifier_free_n.infix(), [i for i in range(len(primitives))])
    step2 = prover.add_assumption(quantifier_free)
    prover.add_tautological_inference(goal, [step1, step2])

    return prover.proof


def combine_contradictions(proof_true, proof_false):
    """ Given two proofs of contradictions from two lists of assumptions that
        differ only in the last assumption, where the last assumption of
        proof_false is the negation of that of proof_true, return a proof of a
        contradiction from only the assupmtions common to both proofs (without
        the last assumption of each proof). You can assume that each of the
        given proofs has Prover.AXIOMS (in order) as its first six
        axioms/assumptions, and that all of its axioms/assumptions are
        sentences """
    assert type(proof_true) is Proof and type(proof_false) is Proof
    assert proof_true.assumptions[:-1] == proof_false.assumptions[:-1]
    assert proof_false.assumptions[-1].templates == set()
    assert proof_true.assumptions[-1].templates == set()
    assert proof_false.assumptions[-1].formula == \
           Formula('~', proof_true.assumptions[-1].formula)
    # Task 12.4


def eliminate_universal_instance_assumption(proof, constant):
    """ Given a proof of a contradiction from a list of assumptions, where the
        last assumption is an instantiation of the form 'formula(consatnt)'
        (for the given constant name) of the universal assumption of the form
        'Ax[formula(x)]' that immediately precedes it, return a proof of a
        contradiction from the same assumptions without the last (universally
        instantiated) one. You can assume that the given proof has
        Prover.AXIOMS (in order) as its first six axioms/assumptions, and that
        all of its axioms/assumptions are sentences """
    assert type(proof) is Proof
    assert proof.assumptions[-2].templates == set()
    assert proof.assumptions[-1].templates == set()
    assert proof.assumptions[-2].formula.root == "A"
    assert proof.assumptions[-1].formula == \
           proof.assumptions[-2].formula.predicate.substitute(
               {proof.assumptions[-2].formula.variable: Term(constant)})
    # Task 12.5


def universally_close(sentences, constants):
    """ Return a set of sentences that contains the given set of
        prenex-normal-form sentences and is universally closed with respect to
        the given set of constant names. For example, if sentences is the
        singleton {'Ax[Ay[R(x,y)]]'} and constants is {a,b}, then the returned
        set should be: {'Ax[Ay[R(x,y)]]', 'Ay[R(a,y)]', 'Ay[R(b,y)]', 'R(a,a)',
        'R(a,b)', 'R(b,a)', 'R(b,b)'} """
    for sentence in sentences:
        assert type(sentence) is Formula and is_in_prenex_normal_form(sentence)
    for constant in constants:
        assert is_constant(constant)
    # Task 12.6


def replace_constant(proof, constant, variable='zz'):
    """ Given a proof, a constant name that (potentially) appears in the
        assumptions and/or proof, and a variable name that does not appear
        anywhere in the proof or assumptions, return a "similar" (and also
        valid) proof where every occurrence of the given constant name in the
        assumptions and proof is replaced with the given variable name. You may
        assume that the given constant name only appears in the assumption
        schemata of the given proof as a non-template constant name """
    assert is_constant(constant)
    assert is_variable(variable)
    assert type(proof) is Proof
    # Task 12.7


def eliminate_existential_witness_assumption(proof, constant):
    """ Given a proof of a contradiction from a list of assumptions, where the
        last assumption is a witness of the form 'formula(constant)' (for the
        given constant name) for the existential assumption of the form
        'Ex[formula(x)]' that immediately precedes it, and where the given
        constant name does not appear anywhere else in the assumptions, return
        a proof of a contradiction from the same assumptions without the last
        (witness) one. You can assume that the given proof has Prover.AXIOMS
        (in order) as its first six axioms/assumptions, and that all of its
        axioms/assumptions are sentences """
    assert type(proof) is Proof
    assert proof.assumptions[-2].templates == set()
    assert proof.assumptions[-1].templates == set()
    assert proof.assumptions[-2].formula.root == "E"
    assert proof.assumptions[-1].formula == \
           proof.assumptions[-2].formula.predicate.substitute(
               {proof.assumptions[-2].formula.variable: Term(constant)})
    # Task 12.8


def existentially_close(sentences, constants):
    """ Return a pair of a set of sentences that contains the given set of
        prenex-normal-form sentences and a set of constant names that contains
        the given set of constant names, such that the returned set of
        sentences is universally closed with respect to the returned set of
        constants names. For example, if sentences is the singleton
        {'Ex[Ey[R(x,y)]]'} and constants is {a,b}, then the returned set could
        be: {'Ex[Ey[R(x,y)]]', 'Ey[R(c1,y)]', 'R(c1,c2)'}. New constant names
        should be generated using next(fresh_constant_name_generator) """
    for sentence in sentences:
        assert type(sentence) is Formula and is_in_prenex_normal_form(sentence)
    for constant in constants:
        assert is_constant(constant)
    # Task 12.9
