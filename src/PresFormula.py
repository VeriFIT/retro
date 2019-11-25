
import itertools
import math
from enum import Enum
from collections import namedtuple
from FAdo.fa import *

PresNFA = namedtuple("PresNFA", "vars nfa")

class PresFormulaType(Enum):
    CONJ = 1
    DISJ = 2
    NEG = 3
    LEQ = 4
    LE = 5
    EQ = 6


class PresFormula:

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


    def translate_to_nfa(self):
        if self.type == PresFormulaType.LEQ:
            print(self.value)
            return PresFormula._leq_to_dfa(self.value[0], self.value[1], self.value[2])
        elif self.type == PresFormulaType.LE:
            print(self.value)
            return PresFormula._leq_to_dfa(self.value[0], self.value[1], self.value[2], True)
        elif self.type == PresFormulaType.EQ:
            print(self.value)
            return PresFormula._eq_to_dfa(self.value[0], self.value[1], self.value[2])
        elif self.type == PresFormulaType.CONJ:
            aut1 = self.formulas[0].translate_to_nfa()
            aut2 = self.formulas[1].translate_to_nfa()
            if aut1.vars != aut2.vars:
                vars = aut1.vars + aut2.vars
                aut1 = PresFormula.expand_aut_vars(aut1, vars)
                aut2 = PresFormula.expand_aut_vars(aut2, vars)
            return PresNFA(vars, aut1.nfa.conjunction(aut2.nfa))
        elif self.type == PresFormulaType.DISJ:
            aut1 = self.formulas[0].translate_to_nfa()
            aut2 = self.formulas[1].translate_to_nfa()
            if aut1.vars != aut2.vars:
                vars = aut1.vars + aut2.vars
                aut1 = PresFormula.expand_aut_vars(aut1, vars)
                aut2 = PresFormula.expand_aut_vars(aut2, vars)
            return PresNFA(vars, aut1.nfa.disjunction(aut2.nfa))
        elif self.type == PresFormulaType.NEG:
            aut = self.formulas[0].translate_to_nfa()
            aut.nfa.setSigma(PresFormula._alphabet(aut.vars))
            compl = aut.nfa.__invert__()
            return PresNFA(aut.vars, compl)
        raise Exception("Not implemented type of formula {0}".format(str(self)))


    def translate_to_nfa_vars(self, vars):
        aut = self.translate_to_nfa()
        return PresFormula.expand_aut_vars(aut, vars)


    def translate_to_nfa_vars_sym(self, vars):
        aut = self.translate_to_nfa()
        return PresFormula.expand_aut_vars_sym(aut, vars)


    @staticmethod
    def _all_combinations(n):
        return list(itertools.product([0, 1], repeat=n))


    @staticmethod
    def _dot_product(a,b):
        assert len(a) == len(b)
        n = len(a)
        ret = 0
        for i in range(0,n):
            ret = ret + (a[i]*b[i])
        return ret


    @staticmethod
    def _create_symbol(vars, vec):
        return frozenset(zip(vars, vec))


    @staticmethod
    def _leq_to_dfa(a_lst, vars, b, strict=False):
        aut = NFA()
        stack = list([b])
        n = len(vars)
        states = set()
        states.add(b)
        aut.addState(b)

        while stack:
            k = stack.pop()
            index_src = aut.stateIndex(k)
            if (not strict) and k >= 0:
                aut.addFinal(index_src)
            if strict and k > 0:
                aut.addFinal(index_src)
            for vec in PresFormula._all_combinations(n):
                j = math.floor((k - PresFormula._dot_product(a_lst,vec))/2.0)
                if not j in states:
                    stack.append(j)
                    states.add(j)
                    aut.addState(j)
                index_dest = aut.stateIndex(j)
                aut.addTransition(index_src, PresFormula._create_symbol(vars, vec), index_dest)
        aut.addInitial(aut.stateIndex(b))

        return PresNFA(set(vars), aut)


    @staticmethod
    def _eq_to_dfa(a_lst, vars, b):
        aut = NFA()
        stack = list([b])
        n = len(vars)
        states = set()
        states.add(b)
        aut.addState(b)

        while stack:
            k = stack.pop()
            index_src = aut.stateIndex(k)
            if k == 0:
                aut.addFinal(index_src)
            for vec in PresFormula._all_combinations(n):
                if (k - PresFormula._dot_product(a_lst,vec)) % 2 != 0:
                    continue
                j = math.floor((k - PresFormula._dot_product(a_lst,vec))/2.0)
                if not j in states:
                    stack.append(j)
                    states.add(j)
                    aut.addState(j)
                index_dest = aut.stateIndex(j)
                aut.addTransition(index_src, PresFormula._create_symbol(vars, vec), index_dest)
        aut.addInitial(aut.stateIndex(b))

        return PresNFA(set(vars), aut)


    @staticmethod
    def _expand_symbol(sym, vars):
        n = len(vars)
        sym_lst = list(sym)
        ret = list()

        if len(vars) == 0:
            return [sym]

        for vec in PresFormula._all_combinations(n):
            ret.append(frozenset(sym_lst + list(PresFormula._create_symbol(vars, vec))))
        return ret


    @staticmethod
    def _expand_symbol_sym(sym, vars):
        n = len(vars)
        sym_lst = list(sym)
        ret = list()

        if n == 0:
            return [sym]

        ret.append(frozenset(sym_lst + list(zip(vars, "?"*n))))
        return ret


    @staticmethod
    def _alphabet(vars):
        n = len(vars)
        return set([PresFormula._create_symbol(vec, vars) for vec in PresFormula._all_combinations(n)])


    @staticmethod
    def _diff(fst, snd):
        snd = set(snd)
        return [item for item in fst if item not in snd]


    @staticmethod
    def expand_aut_vars(pres_aut, new_vars):
        add_vars = PresFormula._diff(new_vars, pres_aut.vars)
        aut_dup = pres_aut.nfa.dup()
        trans = dict()

        for state, dct in pres_aut.nfa.delta.items():
            trans[state] = dict()
            for sym, dst_set in dct.items():
                for ex_symbol in PresFormula._expand_symbol(sym, add_vars):
                    trans[state][ex_symbol] = dst_set
        aut_dup.delta = trans
        return PresNFA(new_vars, aut_dup)


    @staticmethod
    def expand_aut_vars_sym(pres_aut, new_vars):
        add_vars = PresFormula._diff(new_vars, pres_aut.vars)
        aut_dup = pres_aut.nfa.dup()
        trans = dict()

        for state, dct in pres_aut.nfa.delta.items():
            trans[state] = dict()
            for sym, dst_set in dct.items():
                for ex_symbol in PresFormula._expand_symbol_sym(sym, add_vars):
                    trans[state][ex_symbol] = dst_set
        aut_dup.delta = trans
        return PresNFA(new_vars, aut_dup)
