#!/usr/bin/env python3

import ast
from PresFormula import *
from SmtFormula import *
from itertools import chain
from collections import defaultdict
from Symbol import *

conv_map = {EqFormulaType.LEQ: PresFormulaType.LEQ, \
    EqFormulaType.LE: PresFormulaType.LE, EqFormulaType.EQ: PresFormulaType.EQ}

class SmtWrapper:

    def __init__(self, fls):
        self.formulas = fls


    def get_pres_formulas(self):
        ret = list()
        for fl in self.formulas:
            if fl.is_constraint():
                ret.append(SmtWrapper.get_pres_formula(fl))
        return ret


    def get_conj_pres_formula(self):
        ret = list()
        for fl in self.formulas:
            if fl.is_constraint():
                ret.append(SmtWrapper.get_pres_formula(fl))
        if len(ret) == 0:
            return None
        if len(ret) == 1:
            return ret[0]

        fl = PresFormula(PresFormulaType.CONJ, ret[0:2])
        for i in range(2,len(ret)):
            fl = PresFormula(PresFormulaType.CONJ, [fl, ret[i]])
        return fl


    def get_variables(self):
        ret = list()
        for fl in self.formulas:
            if fl.is_var_decl():
                ret.append(fl.formulas[0].value)
        return ret


    def get_str_equations_symbol(self, var_dict):
        ret = list()
        for fl in self.formulas:
            if fl.is_str_equation():
                eq_smt = fl.formulas[0]
                assert eq_smt.type == EqFormulaType.EQ
                left = SmtWrapper.get_str_equation_symbols(eq_smt.formulas[0], var_dict)
                right = SmtWrapper.get_str_equation_symbols(eq_smt.formulas[1], var_dict)
                left, right = SmtWrapper.pad_equation(left, right)
                ret.append(list(zip(left, right)))
        return ret


    def get_str_equations(self, var_dict):
        ret = list()
        for fl in self.formulas:
            if fl.is_str_equation():
                eq_smt = fl.formulas[0]
                assert eq_smt.type == EqFormulaType.EQ
                left = SmtWrapper.get_str_equation_symbols(eq_smt.formulas[0], var_dict)
                right = SmtWrapper.get_str_equation_symbols(eq_smt.formulas[1], var_dict)
                ret.append((left, right))
        return ret


    def get_str_eq_automata(self, eqs, len_constr=None):
        nfa = None
        n = len(eqs)
        for i in range(0, n):
            if i != 0:
                eqs[i].insert(0, (Symbol.delimiter(), Symbol.delimiter()))
            if nfa is not None:
                nfa = nfa.concat(SmtWrapper.nfa_from_string(eqs[i]))
            else:
                nfa = SmtWrapper.nfa_from_string(eqs[i])

        if len_constr is not None:
            delim = SmtWrapper.nfa_from_string([(Symbol.len_delim(), Symbol.len_delim())], False)
            nfa = nfa.concat(delim)
            nfa = nfa.concat(len_constr)
        return nfa


    def len_constr_rename_var(self, var_dict):
        for fl in self.formulas:
            if fl.is_constraint():
                fl.map_variables(lambda x: var_dict[x])


    @staticmethod
    def nfa_from_string(lst, sl=True):
        states = list(range(0,len(lst)))
        ret = NFA()
        i = 0
        for item in lst:
            ret.addState(i)
            ret.addTransition(i, item, i+1)
            i = i + 1
        ret.addState(i)
        if sl:
            ret.addTransition(i, (Symbol.blank(), Symbol.blank()), i)
        ret.addFinal(i)
        ret.addInitial(0)
        return ret



    @staticmethod
    def _pres_type_convert(type):
        return conv_map[type]


    @staticmethod
    def get_pres_formula(smt_formula):
        if smt_formula.type == EqFormulaType.ASSERT:
            assert len(smt_formula.formulas) == 1
            return SmtWrapper.get_pres_formula(smt_formula.formulas[0])
        if smt_formula.type in [EqFormulaType.LEQ, EqFormulaType.LE, EqFormulaType.EQ]:
            assert len(smt_formula.formulas) == 2
            a_dict = SmtWrapper.get_lin_vector(smt_formula.formulas[0])
            b_dict = SmtWrapper.get_lin_vector(smt_formula.formulas[1])
            return PresFormula(SmtWrapper._pres_type_convert(smt_formula.type), [], SmtWrapper.get_pres_triple(a_dict, b_dict))
        if smt_formula.type in [EqFormulaType.GEQ, EqFormulaType.GE]:
            assert len(smt_formula.formulas) == 2
            type = PresFormulaType.LE if smt_formula.type == EqFormulaType.GEQ else PresFormulaType.LEQ
            a_dict = SmtWrapper.get_lin_vector(smt_formula.formulas[0])
            b_dict = SmtWrapper.get_lin_vector(smt_formula.formulas[1])
            return PresFormula(PresFormulaType.NEG, [PresFormula(type, [], SmtWrapper.get_pres_triple(a_dict, b_dict))])


    @staticmethod
    def get_pres_triple(a_dict, b_dict):
        ret = defaultdict(int)
        for k, v in a_dict.items():
            ret[k] = v
        for k, v in b_dict.items():
            ret[k] = ret[k] - v

        b = -ret["_const_"]
        del ret["_const_"]
        lst = list(ret.items())
        vars = list(map(lambda x: x[0], lst))
        a_vec = list(map(lambda x: x[1], lst))
        return a_vec, vars, b


    @staticmethod
    def _plus_merge(a_dict, b_dict):
        ret = defaultdict(int)
        for k, v in chain(a_dict.items(), b_dict.items()):
            ret[k] += v
        return ret


    @staticmethod
    def _lin_mult_merge(a_dict, b_dict):
        assert len(a_dict) == 1 or len(b_dict) == 1
        dct = dict()
        mult = 1
        if len(a_dict) == 1 and "_const_" in a_dict:
            mult = a_dict["_const_"]
            dct = b_dict
        else:
            mult = b_dict["_const_"]
            dct = a_dict
        return {k: (mult*v) for k, v in dct.items()}


    @staticmethod
    def get_lin_vector(smt_formula):
        if smt_formula.type == EqFormulaType.CONST:
            return {"_const_": smt_formula.value}
        if smt_formula.type == EqFormulaType.VAR:
            return {smt_formula.value: int(1)}
        if smt_formula.type == EqFormulaType.MULT:
            assert len(smt_formula.formulas) == 2
            return SmtWrapper._lin_mult_merge(SmtWrapper.get_lin_vector(smt_formula.formulas[0]), \
                SmtWrapper.get_lin_vector(smt_formula.formulas[1]))
        if smt_formula.type == EqFormulaType.PLUS:
            assert len(smt_formula.formulas) == 2
            return SmtWrapper._plus_merge(SmtWrapper.get_lin_vector(smt_formula.formulas[0]), \
                SmtWrapper.get_lin_vector(smt_formula.formulas[1]))
        if smt_formula.type == EqFormulaType.LEN:
            assert len(smt_formula.formulas) == 1
            return SmtWrapper.get_lin_vector(smt_formula.formulas[0])
        raise Exception("Unsupported behaviour")


    @staticmethod
    def get_str_equation_symbols(smt_formula, var_dict):
        if smt_formula.type == EqFormulaType.CONCAT:
            assert len(smt_formula.formulas) == 2
            return SmtWrapper.get_str_equation_symbols(smt_formula.formulas[0], var_dict) + \
                SmtWrapper.get_str_equation_symbols(smt_formula.formulas[1], var_dict)
        if smt_formula.type == EqFormulaType.VAR:
            return [var_dict[smt_formula.value]]
        if smt_formula.type == EqFormulaType.LITER:
            str = ast.literal_eval("\"{0}\"".format(smt_formula.value))
            return list(map(lambda x: Symbol(False, ord(x)), str))
        raise Exception("Unsupported type of formula {0}".format(smt_formula))


    @staticmethod
    def pad_equation(left, right):
        diff = len(left) - len(right)
        if diff <= 0:
            left = left + abs(diff)*[Symbol.blank()]
        else:
            right = right + diff*[Symbol.blank()]
        return left, right
