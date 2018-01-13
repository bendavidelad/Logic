""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/some_proofs.py """

from predicates.prover import *


def lovers_proof(print_as_proof_forms=False):
    """ Return a proof that from assumptions (in addition to Prover.AXIOMS):
        1) Everybody loves somebody and
        2) Everybody loves a lover
        derives the conclusion:
        Everybody loves everybody.
        The Boolean flag print_as_proof_forms specifies whether the proof being
        constructed is to be printed in real time as it is being constructed """
    prover = Prover(['Ax[Ey[Loves(x,y)]]', 'Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]'],
                    'Ax[Az[Loves(z,x)]]', print_as_proof_forms)
    # Task 10.4
    step1 = prover.add_assumption('Ax[Ey[Loves(x,y)]]')
    step2 = prover.add_assumption('Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]')
    step3 = prover.add_universal_instantiation('Ey[Loves(x,y)]', step1, 'x')
    step4 = prover.add_universal_instantiation('Az[Ay[(Loves(x,y)->Loves(z,x))]]', step2, 'x')
    step5 = prover.add_universal_instantiation('Ay[(Loves(x,y)->Loves(z,x))]', step4, 'z')
    step6 = prover.add_universal_instantiation('(Loves(x,y)->Loves(z,x))', step5, 'y')
    step7 = prover.add_existential_derivation('Loves(z,x)', step3, step6)
    step8 = prover.add_ug('Az[Loves(z,x)]', step7)
    step9 = prover.add_ug('Ax[Az[Loves(z,x)]]', step8)
    return prover.proof


def homework_proof(print_as_proof_forms=False):
    """ Return a proof that from the assumptions (in addition to Prover.AXIOMS):
        1) No homework is fun, and
        2) Some reading is homework
        derives the conclusion:
        Some reading is not fun.
        The Boolean flag print_as_proof_forms specifies whether the proof being
        constructed is to be printed in real time as it is being constructed """
    prover = Prover(['~Ex[(Homework(x)&Fun(x))]', 'Ex[(Homework(x)&Reading(x))]'],
                    'Ex[(Reading(x)&~Fun(x))]', print_as_proof_forms)
    # Task 10.5
    step1 = prover.add_assumption('~Ex[(Homework(x)&Fun(x))]')
    step2 = prover.add_assumption('Ex[(Homework(x)&Reading(x))]')
    step3 = prover.add_instantiated_assumption('((Homework(x)&Fun(x))->Ex[(Homework(x)&Fun(x))])', Prover.EI,
                                               {'R(v)': '(Homework(v)&Fun(v))', 'c': 'x'})
    step4 = prover.add_tautological_inference('(~(Homework(x)&Fun(x)))', [step1, step3])
    step5 = prover.add_tautological_inference('(Homework(x)->~Fun(x))', [step4])
    step6 = prover.add_tautological_inference('((Homework(x)&Reading(x))->(Reading(x)&~Fun(x)))', [step5])
    step7 = prover.add_instantiated_assumption('((Reading(x)&~Fun(x))->Ex[(Reading(x)&~Fun(x))])', Prover.EI,
                                               {'R(v)': '(Reading(v)&~Fun(v))', 'c': 'x'})
    step8 = prover.add_tautological_inference('((Homework(x)&Reading(x))->Ex[(Reading(x)&~Fun(x))])',
                                              [step7, step6])
    step9 = prover.add_existential_derivation('Ex[(Reading(x)&~Fun(x))]', step2, step8)
    return prover.proof


GROUP_AXIOMS = ['plus(0,x)=x', 'plus(minus(x),x)=0',
                'plus(plus(x,y),z)=plus(x,plus(y,z))']


def unique_zero_proof(print_as_proof_forms=False):
    """ Return a proof that from the group axioms (in addition to Prover.AXIOMS)
        and from the assumption a+c=a proves c=0. The Boolean flag
        print_as_proof_forms specifies whether the proof being constructed is
        to be printed in real time as it is being constructed """
    prover = Prover(GROUP_AXIOMS + ['plus(a,c)=a'], 'c=0', print_as_proof_forms)
    # Task 10.10
    step1 = prover.add_assumption('plus(a,c)=a')
    step2 = prover.add_flipped_equality('a=plus(a,c)', step1)
    term_with_free_v = 'plus(minus(a),v)'
    step3 = prover.add_substituted_equality('plus(minus(a),a)=plus(minus(a),plus(a,c))', step2,
                                            term_with_free_v)
    step4 = prover.add_assumption('plus(plus(x,y),z)=plus(x,plus(y,z))')
    step5 = prover.add_free_instantiation('plus(plus(minus(a),a),c)=plus(minus(a),plus(a,c))', step4,
                                          {'x': 'minus(a)', 'y': 'a', 'z': 'c'})
    step6 = prover.add_flipped_equality('plus(minus(a),plus(a,c))=plus(plus(minus(a),a),c)', step5)
    step7 = prover.add_chained_equality('plus(minus(a),a)=plus(plus(minus(a),a),c)', [step3, step6])
    step8 = prover.add_assumption('plus(minus(x),x)=0')
    step9 = prover.add_free_instantiation('plus(minus(a),a)=0', step8, {'x': 'a'})
    term_with_free_v_2 = 'plus(v,c)'
    step10 = prover.add_substituted_equality('plus(plus(minus(a),a),c)=plus(0,c)', step9, term_with_free_v_2)
    step11 = prover.add_chained_equality('plus(minus(a),a)=plus(0,c)', [step7, step10])
    step12 = prover.add_flipped_equality('plus(0,c)=plus(minus(a),a)', step11)
    step13 = prover.add_chained_equality('plus(0,c)=0', [step12, step9])
    step14 = prover.add_assumption('plus(0,x)=x')
    step15 = prover.add_free_instantiation('plus(0,c)=c', step14, {'x': 'c'})
    step16 = prover.add_flipped_equality('0=plus(0,c)', step13)
    step17 = prover.add_chained_equality('0=c', [step16, step15])
    step18 = prover.add_flipped_equality('c=0', step17)
    return prover.proof


FIELD_AXIOMS = GROUP_AXIOMS + ['plus(x,y)=plus(y,x)', 'times(x,1)=x',
                               'times(x,y)=times(y,x)',
                               'times(times(x,y),z)=times(x,times(y,z))',
                               '(~x=0->Ey[times(y,x)=1])',
                               'times(x,plus(y,z))=plus(times(x,y),times(x,z))']


def multiply_zero_proof(print_as_proof_forms=False):
    """ Return a proof that from the field axioms (in addition to Prover.AXIOMS)
        proves 0*x=0. The Boolean flag print_as_proof_forms specifies whether
        the proof being constructed is to be printed in real time as it is
        being constructed """
    prover = Prover(FIELD_AXIOMS, 'times(0,x)=0', print_as_proof_forms)
    # Task 10.11
    step1 = prover.add_assumption('plus(0,x)=x')
    step2 = prover.add_free_instantiation('plus(0,0)=0', step1, {'x': '0'})
    step3 = prover.add_substituted_equality('times(x,plus(0,0))=times(x,0)', step2, 'times(x,v)')
    step31 = prover.add_flipped_equality('times(x,0)=times(x,plus(0,0))', step3)
    step4 = prover.add_assumption('times(x,plus(y,z))=plus(times(x,y),times(x,z))')
    step5 = prover.add_free_instantiation('times(x,plus(0,0))=plus(times(x,0),times(x,0))', step4,
                                          {'x': 'x', 'y': '0', 'z': '0'})
    step6 = prover.add_chained_equality('times(x,0)=plus(times(x,0),times(x,0))', [step31, step5])
    step7 = prover.add_assumption('plus(minus(x),x)=0')
    step8 = prover.add_free_instantiation('plus(minus(times(x,0)),times(x,0))=0', step7,
                                          {'x': 'times(x,0)'})
    step9 = prover.add_flipped_equality('0=plus(minus(times(x,0)),times(x,0))', step8)
    step10 = prover.add_substituted_equality(
        'plus(minus(times(x,0)),times(x,0))=plus(minus(times(x,0)),plus(times(x,0),times(x,0)))', step6,
        'plus(minus(times(x,0)),v)')
    step11 = prover.add_assumption('plus(plus(x,y),z)=plus(x,plus(y,z))')
    step12 = prover.add_flipped_equality('plus(x,plus(y,z))=plus(plus(x,y),z)', step11)
    step13 = prover.add_free_instantiation(
        'plus(minus(times(x,0)),plus(times(x,0),times(x,0)))='
        'plus(plus(minus(times(x,0)),times(x,0)),times(x,0))',
        step12, {'x': 'minus(times(x,0))', 'y': 'times(x,0)', 'z': 'times(x,0)'})

    step14 = prover.add_substituted_equality(
        'plus(plus(minus(times(x,0)),times(x,0)),times(x,0))=plus(0,times(x,0))', step8, 'plus(v,times(x,0))')
    step15 = prover.add_free_instantiation('plus(0,times(x,0))=times(x,0)', step1, {'x': 'times(x,0)'})
    step16 = prover.add_chained_equality('0=times(x,0)', [step9, step10, step13, step14, step15])
    step17 = prover.add_flipped_equality('times(x,0)=0', step16)
    step18 = prover.add_assumption('times(x,y)=times(y,x)')
    step19 = prover.add_free_instantiation('times(0,x)=times(x,0)', step18, {'x': '0', 'y': 'x'})
    step20 = prover.add_chained_equality('times(0,x)=0', [step19,step17])
    return prover.proof


PEANO_AXIOMS = ['(s(x)=s(y)->x=y)', '(~x=0->Ey[s(y)=x])', '~s(x)=0',
                'plus(x,0)=x', 'plus(x,s(y))=s(plus(x,y))', 'times(x,0)=0',
                'times(x,s(y))=plus(times(x,y),x)',
                Schema('((R(0)&Ax[(R(x)->R(s(x)))])->Ax[R(x)])', 'R')]


def peano_zero_proof(print_as_proof_forms=False):
    """ Return a proof that from the Peano axioms (in addition to Prover.AXIOMS)
        proves 0+x=x. The Boolean flag print_as_proof_forms specifies whether
        the proof being constructed is to be printed in real time as it is
        being constructed """
    prover = Prover(PEANO_AXIOMS, 'plus(0,x)=x', print_as_proof_forms)
    # Task 10.12
    line1 = prover.add_assumption('plus(x,0)=x')
    line2 = prover.add_assumption('plus(x,s(y))=s(plus(x,y))')
    line3 = prover.add_free_instantiation('plus(0,0)=0', line1, {'x': '0'})
    line4 = prover.add_instantiated_assumption(
        '(plus(0,x)=x->(plus(0,s(x))=s(plus(0,x))->plus(0,s(x))=s(x)))',
        Prover.ME, {'R(v)': 'plus(0,s(x))=s(v)', 'c': 'plus(0,x)', 'd': 'x'})
    line5 = prover.add_free_instantiation('plus(0,s(x))=s(plus(0,x))', line2, {'x': '0', 'y': 'x'})
    line6 = prover.add_tautological_inference('(plus(0,x)=x->plus(0,s(x))=s(x))', [line5, line4])
    line7 = prover.add_ug('Ax[(plus(0,x)=x->plus(0,s(x))=s(x))]', line6)
    line8 = prover.add_tautological_inference('(plus(0,0)=0&Ax[(plus(0,x)=x->plus(0,s(x))=s(x))])',
                                              [line3, line7])
    line9 = prover.add_instantiated_assumption(
        '((plus(0,0)=0&Ax[(plus(0,x)=x->plus(0,s(x))=s(x))])->Ax[plus(0,x)=x])', PEANO_AXIOMS[-1],
        {'R(v)': 'plus(0,v)=v'}
    )
    line10 = prover.add_mp('Ax[plus(0,x)=x]', line8, line9)
    line11 = prover.add_universal_instantiation('plus(0,x)=x', line10, 'x')
    return prover.proof


COMPREHENSION_AXIOM = Schema('Ey[Ax[((In(x,y)->R(x))&(R(x)->In(x,y)))]]', {'R'})


def russell_paradox_proof(print_as_proof_forms=False):
    """ Return a proof that from the axiom schema of (unrestricted)
        comprehension (in addition to Prover.AXIOMS) proves the falsehood
        (z=z&~z=z). The Boolean flag print_as_proof_forms specifies whether the
        proof being constructed is to be printed in real time as it is being
        constructed """
    prover = Prover([COMPREHENSION_AXIOM], '(z=z&~z=z)', print_as_proof_forms)
    step1 = prover.add_instantiated_assumption('Ey[Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]]',
                                               COMPREHENSION_AXIOM, {'R(v)': '~In(v,v)'})
    step2 = prover.add_instantiated_assumption(
        '(Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]->((In(y,y)->~In(y,y))&(~In(y,y)->In(y,y))))',
        Prover.UI,
        {'R(v)': '((In(v,y)->~In(v,v))&(~In(v,v)->In(v,y)))', 'x': 'x', 'c': 'y'})
    step3 = prover.add_tautology('(((In(y,y)->~In(y,y))&(~In(y,y)->In(y,y)))->(z=z&~z=z))')
    step4 = prover.add_tautological_inference('(Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]->(z=z&~z=z))',
                                              [step2, step3])
    step5 = prover.add_existential_derivation('(z=z&~z=z)', step1, step4)
    return prover.proof
