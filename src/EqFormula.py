
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


class EqFormula:

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
        elif self.type == EqFormulaType.VAR or self.type == EqFormulaType.LITER:
            return True
        else:
            return False


    def is_constraint(self):
        if self.type in [EqFormulaType.ASSERT, EqFormulaType.EQ, \
            EqFormulaType.LE, EqFormulaType.LEQ, EqFormulaType.GE, \
            EqFormulaType.GEQ]:
            for fl in self.formulas:
                if not fl.is_str_equation():
                    return False
        elif self.type == EqFormulaType.VAR or self.type == EqFormulaType.CONST:
            return True
        else:
            return False
