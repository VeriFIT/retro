
from enum import Enum
from collections import namedtuple
from FAdo.fa import *


class EqFormulaType(Enum):
    VAR = 0
    CONST = 1
    CONCAT = 2
    EQ = 3
    LE = 4
    LEQ = 5
    GE = 6
    GEQ = 7
    LEN = 8
    DECL = 9
    ASSERT = 10
    CHECK = 11
    LITER = 12
    LOGIC_DECL = 13
    MULT = 14
    PLUS = 15


class SmtFormula:

    def __init__(self, type, formulas, value=None):
        self.type = type
        self.formulas = formulas
        self.value = value


    def __str__(self):
        ret = str()
        all = ", ".join([str(fl) for fl in self.formulas])
        ret += "({0} {1} {2})".format(self.type, self.value, all)
        return ret

    def __repr__(self):
        return self.__str__()


    def __eq__(self, other):
        return (self.type == other.type) and (self.value == other.value) and (self.formulas == other.formulas)


    def get_decl_name(self):
        if self.type != EqFormulaType.DECL:
            return None
        if len(self.formulas) == 0:
            raise Exception("Empty definition")
        if self.formulas[0].type != EqFormulaType.VAR:
            raise Exception("Only variable definition is allowed")
        return self.formulas[0].value


    def is_var_decl(self):
        return self.type == EqFormulaType.DECL


    def is_str_equation(self):
        if self.type in [EqFormulaType.ASSERT, EqFormulaType.EQ, EqFormulaType.CONCAT]:
            for fl in self.formulas:
                if not fl.is_str_equation():
                    return False
            return True
        elif self.type == EqFormulaType.VAR or self.type == EqFormulaType.LITER:
            return True
        else:
            return False


    def is_constraint(self):
        if self.type in [EqFormulaType.ASSERT, EqFormulaType.EQ, \
            EqFormulaType.LE, EqFormulaType.LEQ, EqFormulaType.GE, \
            EqFormulaType.GEQ, EqFormulaType.MULT, EqFormulaType.PLUS]:
            for fl in self.formulas:
                if not fl.is_constraint():
                    return False
            return True
        elif self.type == EqFormulaType.LEN:
            assert len(self.formulas) == 1
            if self.formulas[0].type == EqFormulaType.VAR or self.formulas[0].type == EqFormulaType.CONST:
                return True
            return False
        elif self.type == EqFormulaType.CONST:
            return True
        else:
            return False


    def get_variables(self):
        if self.type == EqFormulaType.VAR:
            return [self.value]
        ret = list()
        for fl in self.formulas:
            if fl is not None:
                ret = ret + fl.get_variables()
        return ret


    def count_items(self):
        if self.type == EqFormulaType.VAR:
            return 1
        if self.type == EqFormulaType.LITER:
            return len(self.value)
        ret = 0
        for fl in self.formulas:
            if fl is not None:
                ret = ret + fl.count_items()
        return ret


    def map_variables(self, mp):
        if self.type == EqFormulaType.VAR:
            self.value = mp(self.value)
        else:
            for fl in self.formulas:
                fl.map_variables(mp)


    def get_eq_sides(self):
        if self.type == EqFormulaType.ASSERT:
            if self.formulas[0].type == EqFormulaType.EQ:
                return self.formulas[0].formulas
        return None


    def to_smt_str(self):
        val = str()
        for fl in self.formulas:
            val += fl.to_smt_str() + " "
        if self.type == EqFormulaType.ASSERT:
            return "(assert {0})".format(val)
        if self.type == EqFormulaType.EQ:
            return "(= {0})".format(val)
        if self.type == EqFormulaType.CONCAT:
            return "(str.++ {0})".format(val)
        if self.type == EqFormulaType.LITER:
            return "\"{0}\"".format(self.value)
        if self.type == EqFormulaType.VAR:
            return str(self.value)
        raise Exception("Unimplemented {0}".format(self))


    def substitute_vars(self, var_dict):
        if self.type == EqFormulaType.VAR:
            try:
                val = var_dict[self.value]
                self.value = val
                self.type = EqFormulaType.LITER
                self.formulas = []
            except KeyError:
                return
        else:
            for fl in self.formulas:
                fl.substitute_vars(var_dict)


    def get_formula_atoms(self):
        if self.type == EqFormulaType.ASSERT:
            return self.formulas[0].get_formula_atoms()
        if self.type == EqFormulaType.EQ:
            return self.formulas[0].get_formula_atoms(), self.formulas[1].get_formula_atoms()
        if self.type == EqFormulaType.CONCAT:
            return self.formulas[0].get_formula_atoms() + self.formulas[1].get_formula_atoms()
        elif self.type == EqFormulaType.LITER:
            return [self]
        elif self.type == EqFormulaType.VAR:
            return [self]
        raise Exception("Unexpected formula")


    def const_propagation_dict(self):
        var_dict = dict()
        left, right = self.get_formula_atoms()
        lileft = all([x.type == EqFormulaType.LITER for x in left])
        liright = all([x.type == EqFormulaType.LITER for x in right])
        vleft = all([x.type == EqFormulaType.VAR for x in left])
        vright = all([x.type == EqFormulaType.VAR for x in right])
        epsleft = lileft and all([x.value == "" for x in left])
        epsright = liright and all([x.value == "" for x in right])

        if len(left) == 1 and vleft and liright:
            var_dict[left[0].value] = "".join([x.value for x in right])
        elif len(right) == 1 and vright and lileft:
            var_dict[right[0].value] = "".join([x.value for x in left])
        elif vleft and epsright:
            for item in left:
                var_dict[item.value] = ""
        elif vright and epsleft:
            for item in right:
                var_dict[item.value] = ""
        return var_dict


    @staticmethod
    def native_to_smt_atom(atom):
        if not atom.startswith("\""):
            return SmtFormula(EqFormulaType.VAR, [], atom)
        else:
            return SmtFormula(EqFormulaType.LITER, [], atom[1:-1])


    @staticmethod
    def native_to_smt_side(side):
        if len(side) == 0:
            raise Exception("Empty side {0}".format(side))
        if len(side) == 1:
            return SmtFormula.native_to_smt_atom(side[0])

        ret = SmtFormula.native_to_smt_side(side[0:-1])
        at = SmtFormula.native_to_smt_atom(side[-1])
        return SmtFormula(EqFormulaType.CONCAT, [ret, at])


    @staticmethod
    def from_native_to_smt(left, right):
        l_smt = SmtFormula.native_to_smt_side(left)
        r_smt = SmtFormula.native_to_smt_side(right)
        return SmtFormula(EqFormulaType.ASSERT, [SmtFormula(EqFormulaType.EQ, [l_smt, r_smt])])
