
#import RRTransducer
from Symbol import *
#from NFAOperation import *

from FAdo.fa import *


class LabelNFA:

    def __init__(self, fa=NFA(), lb=dict()):
        self.nfa = fa
        self.label = lb


    # def __eq__(self, other):
    #     return self.nfa == other.nfa


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


    # def toDFA(self):
    #     dfa = self.nfa.toDFA()
    #     lab = dict()
    #     for st in dfa.States:
    #         if isinstance(st, set):
    #             ns = frozenset(st)
    #             lab[ns] = str()
    #             for n in ns:
    #                 lab[ns] += " X " + str(self.label[n])
    #         else:
    #             lab[st] = self.label[st]
    #     return LabelNFA(dfa, lab)


    def split_automata(self):
        nfas = list()
        lbl = list()
        states = set()
        for ini in self.nfa.Initial:
            try:
                for _, dst_set in self.nfa.delta[ini].items():
                    for st in dst_set:
                        states.add(st)
            except KeyError:
                return [deepcopy(self)]

        for st in states:
            dl = states - set([st])
            fa = self.nfa.dup()

            for ini in self.nfa.Initial:
                for sym, dst_set in self.nfa.delta[ini].items():
                    for st in dst_set & dl:
                        fa.delTransition(ini, sym, st)
            fa = fa.trim()
            if fa not in nfas:
                lbl.append(LabelNFA(fa, deepcopy(self.label)))
                nfas.append(fa)


        return lbl


    def eliminateEpsilonTransitions(self):
        self.nfa.eliminateEpsilonTransitions()
        return self


    @staticmethod
    def unionFromList(lst):
        ret = LabelNFA()
        for aut in lst:
            ret = ret.disjointUnion(aut)
        return ret



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
            label[new] = self.label[orig_p]

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


    def disjointUnion(self, fa2):
        nfa = self.nfa.dup()
        label = copy(self.label)
        st_num = len(self.nfa.States)
        for st in range(st_num, st_num + len(fa2.nfa.States)):
            nfa.addState(st)
            if st >= st_num:
                label[st] = fa2.label[LabelNFA._set_convert(fa2.nfa.States[st-st_num])]
        for fn in fa2.nfa.Final:
            nfa.addFinal(fn+st_num)
        for ini in fa2.nfa.Initial:
            nfa.addInitial(ini+st_num)

        trans = dict()
        for src, dct in fa2.nfa.delta.items():
            for sym, dst_set in dct.items():
                for dst in dst_set:
                    nfa.addTransition(src+st_num, sym, dst+st_num)
        return LabelNFA(nfa, label)
