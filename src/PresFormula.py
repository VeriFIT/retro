
import intertools
from enum import Enum
from collections import namedtuple
from FAdo.fa import *

PresNFA = namedtuple("PresNFA", "vars nfa")

class PresFormulaType(Enum):
    ATOM = 0
    CONJ = 1
    DISJ = 2
    NEG = 3


class PresFormula:

    def __init__(self, type, formulas, value=None):
        self.type = type
        self.formulas = formulas
        self.value = value


    def translate_to_nfa(self):
        if self.type == ATOM:
            return PresFormula._atom_to_dfa(self.type[0], self.type[1], self.type[2])
        elif self.type == CONJ:
            aut1 = self.formulas[0].translate_to_nfa()
            aut2 = self.formulas[1].translate_to_nfa()
            if aut1.vars != aut2.vars:
                vars = aut1.vars + aut2.vars
                aut1 = PresFormula._expand_aut_vars(aut1, vars)
                aut2 = PresFormula._expand_aut_vars(aut2, vars)
            return PresNFA(vars, aut1.nfa.conjunction(aut2.nfa))
        elif self.type == CONJ:
            aut1 = self.formulas[0].translate_to_nfa()
            aut2 = self.formulas[1].translate_to_nfa()
            if aut1.vars != aut2.vars:
                vars = aut1.vars + aut2.vars
                aut1 = PresFormula._expand_aut_vars(aut1, vars)
                aut2 = PresFormula._expand_aut_vars(aut2, vars)
            return PresNFA(vars, aut1.nfa.conjunction(aut2.nfa))
        elif self.type == NEG:
            aut = self.formulas[0].translate_to_nfa()
            aut.nfa.setSigma(PresFormula._alphabet(new_vars))
            compl = aut.nfa.__invert__()
            return PresNFA(aut.vars, compl)
        raise Exception("Not implemented type of formula.")


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
    def _atom_to_dfa(a_lst, vars, b):
        aut = NFA()
        stack = list([b])
        n = len(vars)
        states = set()

        while stack:
            k = stack.pop()
            states.add(k)
            index_src = aut.addState(k)
            if k >= 0:
                aut.addFinal(index_src)

            for vec in PresFormula._all_combinations(n):
                j = math.floor((k - PresFormula._dot_product(a_lst,vec))/2.0)
                if not j in states:
                    stack.append(j)
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
            ret.append(frozenset(sym_list + PresFormula._create_symbol(vars, vec)))
        return ret


    @staticmethod
    def _alphabet(vars):
        n = len(vars)
        return set([PresFormula._create_symbol(vec, vars) for vec in PresFormula._all_combinations(n)])


    @staticmethod
    def _expand_aut_vars(pres_aut, new_vars):
        add_vars = new_vars - pres_aut.vars
        aut_dup = pres_aut.nfa.dup()
        trans = dict()

        for state, dct in pres_aut.nfa.delta.items():
            trans[state] = dict()
            for sym, dst_set in dct.items():
                for ex_symbol in PresFormula._expand_symbol(sym, add_vars):
                    trans[state][ex_symbol] = dst_set
        aut_dup.delta = trans
        return PresNFA(new_vars, aut_dup)
