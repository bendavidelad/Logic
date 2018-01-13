""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/prover.py """

from predicates.syntax import *
from predicates.proofs import *
from predicates.util import *


class Prover:
    """ A class for gradually constructing a first-order Proof for a given
        conclusion, from given assumptions as well as from the six AXIOMS
        Universal Instantiation (UI), Existential Introduction (EI), Universal
        Simplification (US), Existential Simplification (ES), Reflexivity (RX),
        and Meaning of Equality (ME) """
    UI = Schema('(Ax[R(x)]->R(c))', {'R', 'x', 'c'})
    EI = Schema('(R(c)->Ex[R(x)])', {'R', 'x', 'c'})
    US = Schema('(Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))', {'x', 'Q', 'R'})
    ES = Schema('((Ax[(R(x)->Q())]&Ex[R(x)])->Q())', {'x', 'Q', 'R'})
    RX = Schema('c=c', {'c'})
    ME = Schema('(c=d->(R(c)->R(d)))', {'c', 'd', 'R'})
    AXIOMS = [UI, EI, US, ES, RX, ME]

    def __init__(self, assumptions, conclusion, print_as_proof_forms=False):
        """ Constructs a new Prover. Each element in assumptions may either be
            a Schema or a string, with the latter interpreted as a schema with
            no templates whose unique instance is the given string. Any
            element in assumptions that is already in Prover.AXIOMS is ignored
            as an element of assumptions, to avoid duplication. conclusion
            is the conclusion or its string representation. The Boolean flag
            print_as_proof_forms specifies whether the proof being constructed
            is to be printed in real time as it is being constructed """
        self.proof = Proof(Prover.AXIOMS +
                           [Schema(assumption)
                            if type(assumption) is str else assumption
                            for assumption in assumptions
                            if assumption not in Prover.AXIOMS],
                           Formula.parse(conclusion)
                           if type(conclusion) is str else conclusion, [])
        self.print_as_proof_forms = print_as_proof_forms
        if self.print_as_proof_forms:
            print("Starting Proof")
            print("Assumptions: AXIOMS +", assumptions)
            print("Conclusion:", self.proof.conclusion)

    def _add_line(self, statement, justification):
        """ Append to the proof being constructed the validly justified line
            whose formula is statement and whose justification is given. The
            validity of the added line is asserted, and its number in this
            proof is returned """
        assert type(statement) is Formula or type(statement) is str
        if type(statement) is str:
            statement = Formula.parse(statement)
        line = len(self.proof.lines)
        self.proof.lines.append(Proof.Line(statement, justification))
        assert self.proof.verify_justification(line)
        if self.print_as_proof_forms:
            print(str(line) + ")", statement)
        return line

    def add_instantiated_assumption(self, instance, schema, instantiation_map):
        """ Append to the proof being constructed a validly justified line
            whose formula is instance, which is the result of an instantiation
            via instantiation_map of the given schema, which must be one of the
            assumptions/axioms of this proof. The number of the added line in
            this proof is returned """
        assert type(instance) is Formula or type(instance) is str
        assert type(schema) is Schema
        return self._add_line(instance, ('A', self.proof.assumptions.index(schema), instantiation_map))

    def add_assumption(self, assumption):
        """ Append to the proof being constructed a validly justified line
            whose formula is assumption, which is the (unique) instance of a
            schema with no templates that is one of the assumptions/axioms of
            this proof. The number of the added line in this proof is returned
        """
        assert type(assumption) is Formula or type(assumption) is str
        return self.add_instantiated_assumption(assumption, Schema(str(assumption)), {})

    def add_tautology(self, tautology):
        """ Append to the proof being constructed a validly justified line
            whose formula is tautology, which is a tautology. The number of the
            added line in this proof is returned """
        assert type(tautology) is Formula or type(tautology) is str
        return self._add_line(tautology, ('T',))

    def add_mp(self, consequent, antecedent_line, conditional_line):
        """ Append to the proof being constructed a validly justified line
            whose formula is consequent, and which is a return of applying
            Modus Ponens over lines atecedent_line and conditional_line in this
            proof. The number of the added line in this proof is returned """
        assert type(consequent) is Formula or type(consequent) is str
        return self._add_line(consequent,
                              ('MP', antecedent_line, conditional_line))

    def add_ug(self, quantified, unquantified_line):
        """ Append to the proof being constructed a validly justified line
            whose formula is quantified, and which is a return of universal
            generalization over line unquantified_line in this proof. The
            number of the added line in this proof is returned """
        assert type(quantified) is Formula or type(quantified) is str
        return self._add_line(quantified, ('UG', unquantified_line))

    def add_proof(self, conclusion, proof):
        """ Append to the proof being constructed a whole copy of the
            given proof, where the formula of the last line is conclusion.
            The given proof must have the same list of assumptions, and
            this method takes care of the required line-shift in the
            justifications.  The number of the (new) line in this proof
            containing conclusion is returned """
        assert proof.assumptions == self.proof.assumptions
        line_shift = len(self.proof.lines)
        for line in proof.lines:
            if line.justification[0] == 'A' or line.justification[0] == 'T':
                self._add_line(line.formula, line.justification)
            if line.justification[0] == 'MP':
                self.add_mp(line.formula, line.justification[1] + line_shift,
                            line.justification[2] + line_shift)
            if line.justification[0] == 'UG':
                self.add_ug(line.formula, line.justification[1] + line_shift)
        line_number = len(self.proof.lines) - 1
        assert str(self.proof.lines[line_number].formula) == str(conclusion)
        return line_number

    def add_universal_instantiation(self, instantiation, line_number, term):
        """ Append a sequence of validly justified lines to the proof being
            constructed, where the formula of the last line is statement, which
            is an instantiation of the formula in line line_number in this
            proof, where the instantiation is to the universally
            quantified variable appearing at the beginning of the formula in
            the given line number. Example: if line line_number has the formula
            'Ay[Az[f(x,y)=g(z,y)]]', then when calling this method with the
            term 'h(w)', the instantiation should be
            'Az[f(x,h(w))=g(z,h(w))]'. The number of the (new) line in this
            proof containing instantiation is returned """
        # Task 10.1
        temp = self.proof.lines[line_number].formula.predicate.substitute(
            {self.proof.lines[line_number].formula.variable: Term('v')}).infix()
        x_str = '(' + self.proof.lines[line_number].formula.infix() + '->' + instantiation + ')'
        justification = {'R(v)': temp, 'c': term}
        if is_quantifier(x_str[1]):
            justification['x'] = x_str[2:x_str.find('[')]
        step1 = self.add_instantiated_assumption(x_str, self.UI, justification)
        return self.add_mp(instantiation, line_number, step1)

    def add_tautological_inference(self, conclusion, line_numbers):
        """ Add a sequence of validly justified lines to the proof being
            constructed, where the formula of the last line is conclusion,
            which is a tautological inference of the formulae in the lines in
            this proof whose numbers are given in the list line_numbers. The
            number of the (new) line in this proof containing conclusion is
            returned """
        # Task 10.2
        temp = self.proof.lines[line_numbers[0]].formula.infix()
        lines = [temp]
        count, i = 1, 0
        for i in line_numbers[1:]:
            count += 1
            temp = self.proof.lines[i].formula.infix()
            for j in range(len(lines)):
                lines[j] = lines[j] + '->(' + temp
            lines.append(temp)
        s = self.add_tautology('(' + lines[0] + '->' + conclusion + ')' * count)
        if len(lines) > 1:
            for i in range(len(lines) - 1):
                count -= 1
                s = self.add_mp('(' + lines[i + 1] + '->' + conclusion + ')' * count, line_numbers[i], s)
        else:
            return self.add_mp(conclusion, line_numbers[i], s)
        return self.add_mp(conclusion, line_numbers[i + 1], s)

    def add_existential_derivation(self, statement, line1, line2):
        """ Add a sequence of validly justified lines to the proof being
            constructed, where the formula of the last line is statement.
            The formula in line line1 must be of the form 'Ex[cond(x)]' (for
            some variable x), and the formula in line line2 must be of the form
            'cond(x)->statement' (where x is not free is statement). The number
            of the (new) line in this proof containing statement is returned """
        # Task 10.3
        variable = self.proof.lines[line1].formula.variable
        temp = 'A' + variable + '[' + self.proof.lines[line2].formula.infix() + ']'
        step1 = self.add_ug(temp, line2)
        line_str = '((' + temp + '&' + self.proof.lines[line1].formula.infix() + ')->' + self.proof.lines[
            line2].formula.second.infix() + ')'
        sub_map = {'R(v)': self.proof.lines[line2].formula.first.substitute({variable: Term('v')}).infix(),
                   'Q()': self.proof.lines[line2].formula.second.infix()}
        if 'A' in line_str:
            x = line_str[line_str.find('A') + 1:line_str.find('[')]
            sub_map['x'] = x
        elif 'E' in line_str:
            x = line_str[line_str.find('E') + 1:line_str.find('[')]
            sub_map['x'] = x

        step2 = self.add_instantiated_assumption(line_str, self.ES, sub_map)
        return self.add_tautological_inference(statement, [line1, step1, step2])

    def add_flipped_equality(self, flipped, line_number):
        """ Add a sequence of validly justified lines to the proof being
            constructed, where the formula of the last line is flipped,
            which is an equality of the form 'c=d' (for some terms c, d) where
            the formula in line line_numer in this proof is 'd=c'. The number
            of the (new) line in this proof containing flipped is returned """
        # Task 10.6
        tau_eq_sig = self.proof.lines[line_number].formula
        tau = tau_eq_sig.first
        sig = tau_eq_sig.second
        tau_eq_tau = Formula("=", tau, tau)
        sig_eq_tau = Formula("=", sig, tau)
        me_applies = Formula("->", tau_eq_tau, sig_eq_tau)
        me_total = Formula("->", tau_eq_sig, me_applies)
        step1 = self.add_instantiated_assumption(str(me_total), Prover.ME,
                                                 {'R(v)': 'v=' + str(tau), 'c': str(tau), 'd': str(sig)})
        step2 = self.add_mp(str(me_applies), line_number, step1)
        step3 = self.add_instantiated_assumption(str(tau_eq_tau), Prover.RX, {'c': str(tau)})
        step4 = self.add_mp(str(sig_eq_tau), step3, step2)
        assert (str(sig_eq_tau) == flipped)
        return step4

    def add_free_instantiation(self, instantiation, line_number, substitution_map):
        """ Append a sequence of validly justified lines to the proof being
            constructed, where the formula of the last line is statement, which
            is an instantiation of the formula in line line_number in this
            proof, where the instantiation is simultaneously to the free
            variables appearing as keys in the substitution map. Example: if
            line line_number has the formula 'Az[f(x,y)=g(z,y)]', then when
            calling this method with the substitution map {'y':'h(w)'}, the
            instantiation should be 'Az[f(x,h(w))=g(z,h(w))]'. The number of the
            (new) line in this proof containing instantiation is returned """
        # Task 10.7
        new_substitution_map = {}
        lines = self.proof.lines
        current_ui_line = line_number
        for key in substitution_map:
            current_fresh = next(fresh_variable_name_generator)
            new_substitution_map[current_fresh] = substitution_map[key]
            after_ug = "A" + key + "[" + str(lines[current_ui_line].formula) + "]"
            current_ug_line = self.add_ug(after_ug, current_ui_line)
            after_ui = lines[current_ui_line].formula.substitute({key: Term.parse(current_fresh)})
            current_ui_line = self.add_universal_instantiation(str(after_ui), current_ug_line, current_fresh)
        for key in new_substitution_map:
            after_ug = "A" + key + "[" + str(lines[current_ui_line].formula) + "]"
            current_ug_line = self.add_ug(after_ug, current_ui_line)
            after_ui = lines[current_ui_line].formula.substitute({key: Term.parse(new_substitution_map[key])})
            current_ui_line = self.add_universal_instantiation(str(after_ui), current_ug_line,
                                                               new_substitution_map[key])
        assert (instantiation == after_ui)
        return current_ui_line

    def add_substituted_equality(self, substituted, line_number, term_with_free_v):
        """ Add a sequence of validly justified lines to the proof being
            constructed, where the formula of the last line is substituted,
            which is an equality of two terms, each of which is derived by
            substituting a term for the variable v in term_with_free_v. The
            two terms to be substituted for v are the two sides of the equality
            that is the formula in line line_number in this proof. Example: if
            line line_number has the formula 'g(x)=h(y)' and term_with_free_v
            is 'v+7', then substituted should be 'g(x)+7=h(y)+7'. The number of
            the (new) line in this proof containing substituted is returned """
        # Task 10.8
        lines = self.proof.lines
        left_side = lines[line_number].formula.first
        right_side = lines[line_number].formula.second
        term_with_v_as_left = Term.parse(term_with_free_v).substitute({'v': left_side})
        term_with_v_as_right = Term.parse(term_with_free_v).substitute({'v': right_side})
        left_eq_left = Formula("=", term_with_v_as_left, term_with_v_as_left)
        left_eq_right = Formula("=", term_with_v_as_left, term_with_v_as_right)
        me_applies = Formula("->", left_eq_left, left_eq_right)
        me_total = Formula("->", lines[line_number].formula, me_applies)
        step1 = self.add_instantiated_assumption(str(me_total), Prover.ME, {
            'R(v)': str(term_with_v_as_left) + '=' + str(term_with_free_v), 'c': str(left_side),
            'd': str(right_side)})
        step2 = self.add_mp(str(me_applies), line_number, step1)
        step3 = self.add_instantiated_assumption(str(left_eq_left), Prover.RX,
                                                 {'c': str(term_with_v_as_left)})
        step4 = self.add_mp(str(left_eq_right), step3, step2)
        assert (substituted == str(left_eq_right))
        return step4

    def _add_chained_two_equalities(self, line1, line2):
        """ Add a sequence of validly justified lines to the proof being
            constructed, where the formula of the last line is an equality of
            the form 'c=d' (for some terms c, d) where the formulae in lines
            line1 and line2 in this proof are respectively 'c=a' and 'a=d' (for
            some term a). Example: if Line 7 holds 'a=b', and Line 3 holds
            'b=f(b)', then if line1=7 and line2=3, then the formula of the last
            line added will be the chained equality 'a=f(b)'. The number of the
            (new) line in this proof containing the chained equality is
            returned """
        # Task 10.9.1
        lines = self.proof.lines
        a_eq_b = lines[line1].formula
        b_eq_c = lines[line2].formula
        a = a_eq_b.first
        b = a_eq_b.second
        c = b_eq_c.second
        b_eq_a = Formula("=", b, a)
        a_eq_c = Formula("=", a, c)
        step1 = self.add_flipped_equality(b_eq_a, line1)
        me_applies = Formula("->", b_eq_c, a_eq_c)
        me_total = Formula("->", b_eq_a, me_applies)
        step2 = self.add_instantiated_assumption(str(me_total), Prover.ME,
                                                 {'R(v)': 'v=' + str(c), 'c': str(b), 'd': str(a)})
        step3 = self.add_mp(str(me_applies), step1, step2)
        step4 = self.add_mp(str(a_eq_c), line2, step3)
        return step4

    def add_chained_equality(self, chained, line_numbers):
        """ Add a sequence of validly justified lines to the proof being
            constructed, where the formula of the last line is chained, which
            is an equality of the form 'c=d' (for some terms c, d) where the
            formulae in the lines in this proof whose numbers are given in the
            list line_numbers are of the form (in order) 'c=a1', 'a1=a2', ...,
            'an=d' (for some n and some terms a1,a2,...,an). Example: if Line 7
            holds 'a=b', Line 3 holds 'b=f(b)' and Line 9 holds 'f(b)=0', then
            if line_numbers=[7,3,9], then chained should be 'a=0'. The number of
            the (new) line in this proof containing substituted is returned """
        # Task 10.9.2
        iter_lines = iter(line_numbers)
        first_line = next(iter_lines)
        for line_number in iter_lines:
            second_line = line_number
            first_line = self._add_chained_two_equalities(first_line, second_line)
        assert (str(self.proof.lines[first_line].formula) == chained)
        return first_line
