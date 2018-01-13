""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/proofs.py """

from predicates.syntax import *
from propositions.semantics import is_tautology


class Schema:
    """ A schema of first-order formulae. A schema is given by an object of
        type Formula together with a set of constant, variable, and relation
        names that are to be considered as templates. A template constant name
        stands for any term. A template variable name stands for any variable
        name. A template relation name R stands for any first-order formula
        that does not "confuse" variables, that is, it can can refer to
        variables in the schema formula only through its instantiated formal
        parameters. The number of formal parameters of the template must
        be the same as the number of parameters in each relation instantiation
        of the matching relation name in the schema formula """

    def __init__(self, formula, templates=set()):
        """ Create a schema from a string representation of a Formula alongside
            a set of names of elements that are considered to be templates in
            it """
        self.formula = Formula.parse(formula)
        self.templates = templates

    def __repr__(self):
        return "Schema: " + str(self.formula) + " [templates: " + \
               str(self.templates) + "]"

    def __eq__(self, other):
        return type(other) is Schema and self.formula == other.formula and \
               self.templates == other.templates

    def __ne__(self, other):
        return not self == other

    def __hash__(self):
        return hash(str(self))

    class BoundVariableError(Exception):
        """ Raised by instantiate_formula if any non-formal-parameter variable
            that is free in a formula to be substituted for a relation template
            gets bound by the substitution (or is in the set bound_variables).
            See the docstring of instantiate_formula for more details """

        def __init__(self, variable_name, relation_name):
            self.variable_name = variable_name
            self.relation_name = relation_name

    @staticmethod
    def instantiate_formula(formula, constants_and_variables_instantiation_map,
                            relations_instantiation_map, bound_variables):
        """ Return the Formula resulting in simultaneously making the following
            substitutions in formula:
            1) Replace every occurrence of every constant name or variable name
               k that is a key of constants_and_variables_instantiation_map
               with constants_and_variables_instantiation_map[k], which is an
               object of type Term.
            2) Replace every relation instantiation of relation_name that is a
               key of relations_instantiation_map as follows: let
               (formal_parameters,template)=
                   relations_instantiation_map[relation_name],
               then formal_parmeters is an n-tuple of variable names and
               template is an object of type Formula; the free occurrences in
               template of the n variables names in formal_parameters should be
               simultaneously replaced with the respective arguments of the
               relation instantiation in formula (where in each of them all
               relevant variables and constants should be replaced according to
               rule 1) above), and the result should be used to replace the
               corresponding relation instantiation in formula, as long as it
               is legal in the sense specified next, otherwise:
            3) The method should raise a BoundVariableError exception if any
               variable that is free in template (as defined above) except but
               is not in formal_parameters gets bound when substituted into the
               formula, or is in the set of bound_variables.
               Examples: for formula='Ax[Q(z)->R(x)]',
               constants_and_variables_instantiation_map={}, and
               relations_instantiation_map={'Q': (('v',), 'x=v')},
               an exception should be raised since if Q(z) is replaced with
               'x=z' then x becomes bound. For the same arguments but with
               the above relations_instantiation_map replaced with
               {'Q': (('v',), 'y=v')}, an exception is raised if and only if
               'y' is an element of the set bound_variables """
        assert type(formula) is Formula
        for k in constants_and_variables_instantiation_map:
            assert is_constant(k) or is_variable(k)
            assert type(constants_and_variables_instantiation_map[k]) is Term
            if is_variable(k):
                assert is_variable(constants_and_variables_instantiation_map[k].root)
        for k in relations_instantiation_map:
            assert is_relation(k)
            formal_parameters, template = relations_instantiation_map[k]
            for parameter in formal_parameters:
                assert is_variable(parameter)
            assert type(template) is Formula
        for variable in bound_variables:
            assert is_variable(variable)
        # Task 9.3
        new_formula = copy.deepcopy(formula)
        if is_relation(formula.root):
            for val in relations_instantiation_map.values():
                for var in val[1].free_variables():
                    if var in bound_variables and var not in constants_and_variables_instantiation_map:
                        raise Schema.BoundVariableError(var, val)
            for i, term in enumerate(new_formula.arguments):
                new_formula.arguments[i] = term.substitute(constants_and_variables_instantiation_map)
            if formula.root in relations_instantiation_map:
                if not all(k not in bound_variables for k in relations_instantiation_map):
                    raise Schema.BoundVariableError()
                else:
                    formal_var, form = copy.deepcopy(relations_instantiation_map)[formula.root]
                    return form.substitute(dict(zip(formal_var, new_formula.arguments)))
        elif is_binary(new_formula.root):
            new_formula.first = Schema.instantiate_formula(
                new_formula.first, constants_and_variables_instantiation_map, relations_instantiation_map,
                bound_variables)
            new_formula.second = Schema.instantiate_formula(
                new_formula.second, constants_and_variables_instantiation_map, relations_instantiation_map,
                bound_variables)
        elif is_equality(new_formula.root):
            if is_relation(new_formula.first.root):
                new_formula.first = new_formula.first.substitute(relations_instantiation_map)
            else:
                new_formula.first = new_formula.first.substitute(constants_and_variables_instantiation_map)
            if is_relation(new_formula.second.root):
                new_formula.second = new_formula.second.substitute(relations_instantiation_map)
            else:
                new_formula.second = new_formula.second.substitute(constants_and_variables_instantiation_map)

        elif is_quantifier(formula.root):
            new_map = constants_and_variables_instantiation_map
            variable_determine = formula.variable
            if variable_determine in constants_and_variables_instantiation_map:
                variable_determine = constants_and_variables_instantiation_map[variable_determine].infix()
            bound_variables1 = bound_variables | {variable_determine}
            if formula.variable in constants_and_variables_instantiation_map:
                formula.variable = constants_and_variables_instantiation_map[formula.variable].infix()
            return Formula(formula.root, formula.variable, Schema.instantiate_formula(
                formula.predicate, new_map, relations_instantiation_map, bound_variables1))
        elif is_constant(formula.root) or is_variable(formula.root):
            return formula.substitute(constants_and_variables_instantiation_map)
        elif is_unary(new_formula.root):
            new_formula.first = Schema.instantiate_formula(
                new_formula.first, constants_and_variables_instantiation_map, relations_instantiation_map,
                bound_variables)
        return new_formula

    def instantiate(self, instantiation_map):
        """ Return the first-order formula obtained by applying the mapping
            specified by instantiation_map to this schema. For each template
            constant name, the mapping can contain a string representation
            of a term to be substituted for all occurrences of the tempalte
            constant name; for each template variable name, the mapping can
            contain a variable name to be substituted for all occurrences of
            the template variable name; and for each template relation name the
            mapping can have as a key a "signature" specifying formal
            parameters (variable names) for this relation name, and the mapping
            for this key should contain a string representation of a first-
            order formula parametried by these formal parameters, to be
            substituted for all occurrences of the template relation name. For
            example, if we instantiate
            s = Schema('(EQ(c1,c2)->(R(c1)->R(c2))', {'c1', 'c2', 'R'})
            with s.instantiate({'c1':'plus(x,1)', 'c2':'c2', 'R(z)':'Q(z,y)'}),
            the returned Formula object should correspond to the string
            representation '(EQ(plus(x,1),c2)->(Q(plus(x,1),y)->Q(c2,y)))'.
            For any relation signature relation_signature, any free variables
            in the formula instantiation_map[relation_signature] beyond the
            formal parameters (i.e., the arguments/variables in
            relation_signatures) may not appear anywhere in the schema formula.
            If this is violated, then instantiate should return None. For
            example, we can instantiate
            s = Schema('(Q(y)->Ax[R(x)->Q(y)])', {'R', 'Q'})
            with s.instantiate({'R(w)':'w=0', 'Q(v)':'z=v'}) to get the Formula
            object represented by '(z=y->Ax[x=0->z=y])'. However, attempting
            to instantiate this schema with
            s.instantiate({'R(w)': 'w=0', 'Q(v)':'s(x)=v') should return None
            since the assignment to Q(v) may not use any variable name (except
            for the formal parameter v of Q(v)) from the schema formula """
        for variable in instantiation_map:
            assert type(variable) is str and type(instantiation_map[variable]) is str
        # Task 9.4
        try:
            constants_and_variables_instantiation_map = dict()
            relations_instantiation_map = dict()
            bound_variables = set()
            for i in instantiation_map.keys():
                if is_constant(i) or is_variable(i):
                    if i not in self.templates:
                        return None
                    constants_and_variables_instantiation_map[i] = Term.parse(instantiation_map[i])
                elif is_relation(i[:i.find('(')]):
                    if i[:i.find('(')] not in self.templates:
                        return None
                    args = []
                    for arg in Formula.parse(i).arguments:
                        args.append(arg.infix())
                    relations_instantiation_map[(i[:i.find('(')])] = (
                        args, Formula.parse(instantiation_map[i]))
                else:
                    return None
            return Schema.instantiate_formula(self.formula, constants_and_variables_instantiation_map,
                                              relations_instantiation_map, bound_variables)
        except Schema.BoundVariableError:
            return None


class Proof:
    """A Proof of a first-order formula from a list of assumptions/axioms, each
       of which is a scheme. A proof holds a list of lines. Each line in the
       proof may be of one of the following forms:
       1) an instance of one of the assumption/axiom schemes,
       2) a tautology,
       3) derived from two previous lines via Modus Ponens, or
       4) derived from previous lines using universal generalization.
       The proof is valid if each line is validly deduced, and the last line
       deduces the conclusion """

    class Line:
        """ A line in a proof, containing a first-order formula deduced in this
            line, alongside a justification that is a tuple of one of the
            following forms (corresponding to the four respective forms of
            lines listed above):
            1) ('A', assumption, instantiation_map), where assumption is
               an index of an assumption/axiom and instantiation_map is a map
               from the templates of this assumption/axiom to substitution
               elements
            2) ('T',)
            3) ('MP', line1, line2), where line1 and line2 are line indices
            4) ('UG', line), where line is a line index """

        def __init__(self, formula, justification):
            assert type(formula) is Formula
            assert justification[0] in {'A', 'T', 'MP', 'UG'}
            self.formula = formula
            self.justification = justification

        def __repr__(self):
            return str(self.formula) + "     {" + str(self.justification) + "}"

    def __init__(self, assumptions, conclusion, lines):
        assert type(conclusion) is Formula
        for assumption in assumptions:
            assert type(assumption) is Schema
        self.assumptions = assumptions
        self.conclusion = conclusion
        self.lines = lines

    def __repr__(self):
        s = "Assumptions/Axioms:\n"
        for assumption in self.assumptions:
            s = s + str(assumption) + "\n"
        s = s + "Conclusion: " + str(self.conclusion) + "\nProof:\n"
        for line in self.lines:
            s = s + str(line) + "\n"
        return s

    def verify_a_justification(self, line):
        """ Returns whether the line with the given number is a valid
            instantiation of an assumption/axiom given in its justification via
            an instantiation map given in its justification """
        assert line < len(self.lines)
        justification = self.lines[line].justification
        assert justification[0] == 'A'
        assert len(justification) == 3
        assert type(justification[1]) is int
        assert type(justification[2]) is dict
        for variable in justification[2]:
            assert type(variable) is str and type(justification[2][variable]) is str
        # Task 9.5
        schemata = self.assumptions[justification[1]]
        schemata_instance = schemata.instantiate(justification[2])
        if schemata_instance == self.lines[line].formula:
            return True
        else:
            return False

    def verify_t_justification(self, line):
        """ Returns whether the line with the given number is a tautology """
        assert line < len(self.lines)
        justification = self.lines[line].justification
        assert justification[0] == 'T'
        assert len(justification) == 1
        # Task 9.7
        formula = self.lines[line].formula
        prop_formula = PropositionalFormula.from_infix(formula.propositional_skeleton().infix())
        assert type(prop_formula) is PropositionalFormula
        return is_tautology(prop_formula)

    def verify_mp_justification(self, line):
        """ Returns whether the line with the given number is validly obtained
            by applying modus ponens to the previous line given in its
            justification """
        assert line < len(self.lines)
        justification = self.lines[line].justification
        assert justification[0] == 'MP'
        assert len(justification) == 3
        assert type(justification[1]) == int
        assert type(justification[2]) == int
        # Task 9.8
        if justification[1] >= line or justification[2] >= line:
            return False
        conclusion = self.lines[line].formula
        first = self.lines[justification[1]].formula
        first_implies_second = self.lines[justification[2]].formula
        if not first_implies_second.first == first:
            return False
        if not first_implies_second.second == conclusion:
            return False
        return True

    def verify_ug_justification(self, line):
        """ Returns whether the line with the given number a valid universal
            generalization of a previous line given in its justification """
        assert line < len(self.lines)
        justification = self.lines[line].justification
        assert justification[0] == 'UG'
        assert len(justification) == 2
        assert type(justification[1]) == int
        # Task 9.9
        if justification[1] >= line:
            return False
        conclusion = self.lines[line].formula
        if conclusion.root != "A":
            return False
        assumption = self.lines[justification[1]].formula
        if conclusion.predicate != assumption:
            return False
        return True

    def verify_justification(self, line):
        """ Returns whether the line with the given number is validly justified
        """
        justification_type = self.lines[line].justification[0]
        if justification_type == 'A':
            return self.verify_a_justification(line)
        if justification_type == 'T':
            return self.verify_t_justification(line)
        if justification_type == 'MP':
            return self.verify_mp_justification(line)
        if justification_type == 'UG':
            return self.verify_ug_justification(line)
        else:
            assert False

    def is_valid(self):
        """ Returns whether this proof validly proves its conclusion from its
            assumptions/axioms """
        if len(self.lines) == 0 or self.lines[-1].formula != self.conclusion:
            return False
        for line in range(len(self.lines)):
            if not self.verify_justification(line):
                return False
        return True
