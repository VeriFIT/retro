
#import RRTransducer
from Symbol import *
#from NFAOperation import *

from FAdo.fa import *


class LabelNFA:

    def __init__(self):
        self.nfa = NFA()
        self.label = dict()

    def __init__(self, fa, lb):
        self.nfa = fa
        self.label = lb


    def trim(self):
        ret = self.nfa.trim()
        lab = dict()
        for st in ret.States:
            if isinstance(st, set):
                ns = frozenset(st)
                lab[ns] = self.label[ns]
            else:
                lab[st] = self.label[st]
        return LabelNFA(ret, lab)


    def toDFA(self):
        dfa = self.nfa.toDFA()
        lab = dict()
        for st in dfa.States:
            if isinstance(st, set):
                ns = frozenset(st)
                lab[ns] = self.label[list(ns)[0]]
            else:
                lab[st] = self.label[st]
        return LabelNFA(dfa, lab)


    def toNFA(self):
        ret = self.nfa.toNFA()
        return LabelNFA(ret, self.label)


    def minimalHopcroft(self):
        ret = self.nfa.minimalHopcroft()
        lab = dict()
        for st in ret.States:
            lab[frozenset(st)] = self.label[frozenset(st)]
        return LabelNFA(ret, lab)


    @staticmethod
    def _state_dict(state_dict, cnt, states):
        for st in states:
            st_p = st
            if isinstance(st_p, set):
                st_p = frozenset(st_p)
            if st_p not in state_dict:
                state_dict[st_p] = cnt
                cnt += 1
        return state_dict, cnt



    @staticmethod
    def _set_convert(st):
        if isinstance(st, set):
            return frozenset(st)
        return st


    def renameStates(self):
        cnt = 0
        state_dict = dict()
        state_dict, cnt = LabelNFA._state_dict(state_dict, cnt, self.nfa.States)
        ret = NFA()
        label = dict()

        for orig, new in state_dict.items():
            ret.addState(new)
            orig_p = orig
            if isinstance(orig, set):
                orig_p = frozenset(orig)
            label[new] = self.label[frozenset(orig_p)]

        for src, rest in self.nfa.delta.items():
            for sym, dst_set in rest.items():
                for dst in dst_set:
                    src_p = self.nfa.States[src]
                    dst_p = self.nfa.States[dst]
                    if isinstance(self.nfa.States[src], set):
                        src_p = frozenset(self.nfa.States[src])
                    if isinstance(self.nfa.States[dst], set):
                        dst_p = frozenset(self.nfa.States[dst])
                    ret.addTransition(state_dict[src_p], sym, state_dict[dst_p])

        for ini in self.nfa.Initial:
            ini_p = self.nfa.States[ini]
            if isinstance(ini_p, set):
                ini_p = frozenset(ini_p)
            ret.addInitial(state_dict[ini_p])

        for fin in self.nfa.Final:
            fin_p = self.nfa.States[fin]
            if isinstance(fin_p, set):
                fin_p = frozenset(fin_p)
            ret.addFinal(state_dict[fin_p])

        self.nfa = ret
        self.label = label


    def dotFormat(self):
        dup = self.nfa.dup()
        rename_list = list()

        for i in range(len(self.nfa.States)):
            st = self.nfa.States[i]
            dup.renameState(i, "{0} {1}".format(st, self.label[LabelNFA._set_convert(st)]))
        return dup.dotFormat()
