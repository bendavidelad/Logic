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
    prover = Prover(['Ax[Ey[Loves(x,y)]]',
                     'Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]'],
                    'Ax[Az[Loves(z,x)]]', print_as_proof_forms)
    # Task 10.4
    return prover.proof


def homework_proof(print_as_proof_forms=False):
    """ Return a proof that from the assumptions (in addition to Prover.AXIOMS):
        1) No homework is fun, and
        2) Some reading is homework
        derives the conclusion:
        Some reading is not fun.
        The Boolean flag print_as_proof_forms specifies whether the proof being
        constructed is to be printed in real time as it is being constructed """
    prover = Prover(['~Ex[(Homework(x)&Fun(x))]',
                     'Ex[(Homework(x)&Reading(x))]'],
                    'Ex[(Reading(x)&~Fun(x))]', print_as_proof_forms)
    # Task 10.5
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
    return prover.proof


COMPREHENSION_AXIOM = Schema('Ey[Ax[((In(x,y)->R(x))&(R(x)->In(x,y)))]]', {'R'})


def russell_paradox_proof(print_as_proof_forms=False):
    """ Return a proof that from the axiom schema of (unrestricted)
        comprehension (in addition to Prover.AXIOMS) proves the falsehood
        (z=z&~z=z). The Boolean flag print_as_proof_forms specifies whether the
        proof being constructed is to be printed in real time as it is being
        constructed """
    prover = Prover([COMPREHENSION_AXIOM], '(z=z&~z=z)', print_as_proof_forms)
    # Task 10.13
    return prover.proof
