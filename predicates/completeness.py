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
from predicates.deduction import *
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
    for sentence in sentences:
        if not model.evaluate_formula(sentence):
            quantifier_free = find_unsatisfied_quantifier_free_sentence(sentences, constants, model, sentence)
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
    assert proof_false.assumptions[-1].formula == Formula('~', proof_true.assumptions[-1].formula)
    proof1 = proof_by_contradiction(proof_true, proof_true.assumptions[-1].formula.infix())
    proof2 = proof_by_contradiction(proof_false, proof_false.assumptions[-1].formula.infix())
    goal = Formula('&', proof1.conclusion, proof2.conclusion).infix()
    prover = Prover(proof_true.assumptions[:-1], goal)
    step1 = prover.add_proof(proof1.conclusion, proof1)
    step2 = prover.add_proof(proof2.conclusion, proof2)
    prover.add_tautological_inference(goal, [step1, step2])
    return prover.proof


def eliminate_universal_instance_assumption(proof, constant):
    """ Given a proof of a contradiction from a list of assumptions, where the
        last assumption is an instantiation of the form 'formula(constant)'
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
    assert proof.assumptions[-1].formula == proof.assumptions[-2].formula.predicate.substitute(
        {proof.assumptions[-2].formula.variable: Term(constant)})
    # Task 12.5
    new_proof = proof_by_contradiction(proof, proof.assumptions[-1].formula.infix())
    temp = new_proof.conclusion.infix()
    goal = '(~' + temp + '&' + temp + ')'
    prover = Prover(new_proof.assumptions, goal)
    step1 = prover.add_proof(new_proof.conclusion, new_proof)
    step2 = prover.add_assumption(new_proof.assumptions[-1].formula.infix())
    step3 = prover.add_universal_instantiation(proof.assumptions[-1].formula.infix(), step2, constant)
    prover.add_tautological_inference(goal, [step1, step3])
    return prover.proof


def universally_close(sentences, constants):
    """ Return a set of sentences that contains the given set of
        prenex-normal-form sentences and is universally closed with respect to
        the given set of constant names. For example, if sentences is the
        singleton {'Ax[Ay[R(x,y)]]'} and constants is {a,b}, then the returned
        set should be: {'Ax[Ay[R(x,y)]]', 'Ay[R(a,y)]', 'Ay[R(b,y)]', 'R(a,a)',
        'R(a,b)', 'R(b,a)', 'R(b,b)'} """
    for sentence1 in sentences:
        assert type(sentence1) is Formula and is_in_prenex_normal_form(sentence1)
    for constant in constants:
        assert is_constant(constant)
    # Task 12.6
    if not sentences:
        return sentences
    ret = copy.deepcopy(sentences)
    second = set()
    for sentence in sentences:
        if sentence.root == 'A':
            for con in constants:
                r_d = {sentence.variable: Term(con)}
                temp = sentence.predicate.substitute(r_d)
                ret.add(temp)
                if sentence.predicate.root == 'A':
                    second.add(temp)

    return ret | universally_close(second, constants)


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
    new_assumptions = list()
    substituion_map = {constant: Term.parse(variable)}
    for assump in proof.assumptions:
        new_assumptions.append(Schema(str(assump.formula.substitute(substituion_map)), assump.templates))
    new_conclusion = proof.conclusion.substitute(substituion_map)
    new_lines = list()
    for line in proof.lines:
        new_formula = line.formula.substitute(substituion_map)
        new_justification = line.justification
        if line.justification[0] == 'A':
            if len(line.justification[2]) > 0:
                new_dict = copy.deepcopy(line.justification[2])
                for key, value in new_dict.items():
                    new_dict[key] = value.replace(constant, variable)
                new_justification = (line.justification[0], line.justification[1], new_dict)
        new_lines.append(Proof.Line(new_formula, new_justification))
    new_proof = Proof(new_assumptions, new_conclusion, new_lines)
    return new_proof



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
    proof_start = proof_by_contradiction(proof, str(proof.assumptions[-1].formula))
    prover = Prover(proof_start.assumptions, 'Ax[Az[Loves(z,x)]]')
    step1 = prover.add_proof(proof_start.conclusion, proof_start)
    step2 = prover.add_free_instantiation(proof_start.conclusion, len(proof_start.lines) - 1, {constant: 'x'})
    phi_of_x = prover.proof.lines[-1].formula.first
    exist_x = 'Ex[' + phi_of_x + ']'
    neg_exist_x = '~' + exist_x
    step3 = prover.add_tautological_inference(phi_of_x + '->' + neg_exist_x, len(prover.proof.lines) - 1)
    step4 = prover.add_assumption(prover.proof.assumptions[-1])
    step5 = prover.add_existential_derivation(neg_exist_x, step4, step3)
    step6 = prover.add_tautological_inference(exist_x + '&' + neg_exist_x, [step4, step5])
    return prover.proof


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
