
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
            ret = ret + fl.get_variables()
        return ret


    def map_variables(self, mp):
        if self.type == EqFormulaType.VAR:
            self.value = mp(self.value)
        else:
            for fl in self.formulas:
                fl.map_variables(mp)


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


    @staticmethod
    def native_to_smt_atom(atom):
        if atom.startswith("V"):
            return SmtFormula(EqFormulaType.VAR, [], atom)
        else:
            return SmtFormula(EqFormulaType.LITER, [], atom)


    @staticmethod
    def native_to_smt_side(side):
        assert len(side) > 0
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
