#!/usr/bin/env python3

from dataclasses import dataclass
from typing import Callable, List, Tuple, Dict

from FAdo.fa import *

@dataclass
class RRTGuardAct:
    name: str
    vars: List[str]
    pred: Callable

    def __str__(self):
        return self.name


@dataclass
class RRTTransition:
    src: str
    guard: List[RRTGuardAct]
    tape_update: List[Tuple[str, str]]
    reg_update: List[Tuple[str, str]]
    dest: str


class RRTransducer:

    def __init__(self, name, in_vars, out_vars, hist_regs, stack_regs, init, fin, trans):
        self._name = name
        self._in_vars = in_vars
        self._out_vars = out_vars
        self._hist_regs = hist_regs
        self._stack_regs = stack_regs
        self._init = init
        self._fin = fin
        self._trans = trans

    def __str__(self):
        ret = str()
        ret = ret + "Name: {0}\nInput-Track-Vars: {1}\nOutput-Track-Vars: {2}\n"\
            "History-Regs: {3}\nStack-Regs: {4}\nInitial: {5}\nFinal: {6}\n\n".\
            format(' '.join(map(str, self._name)), ' '.join(map(str, self._in_vars)), \
            ' '.join(map(str, self._out_vars)), ' '.join(map(str, self._hist_regs)), \
            ' '.join(map(str, self._stack_regs)), ' '.join(map(str, self._init)), \
            ' '.join(map(str, self._fin)))
        for _, trlist in self._trans.items():
            for tran in trlist:
                grn = list(map(str, tran.guard))
                ret = ret + str(tran.src) + " ({0})\n".format("), (".join(grn))
                ret = ret + "\t({0})\n".format(", ".join(map((lambda x: "{0} <- {1}".format(x[0], x[1])), tran.tape_update)))
                ret = ret + "\t({0})\n".format(", ".join(map(lambda x: "{0} <- {1}".format(x[0], x[1]), tran.reg_update)))
                ret = ret + "\t{0}\n\n".format(tran.dest)
        return ret


    @staticmethod
    def _guard_subs(guard, sub):
        assert len(guard.vars) <= 2
        assert len(sub) == 1

        name = guard.name
        varsk = set(sub.keys())
        vars = [item for item in guard.vars if item not in varsk]
        for var, sb in sub.items():
            name = name.replace(var, sb)
            if guard.vars.index(var) == 0:
                pred = lambda y: guard.pred(sb, y)
            else:
                pred = lambda y: guard.pred(y, sb)
        return RRTGuardAct(name, vars, pred)


    def _guard_sat(self, varsym, guards):
        assert len(varsym) == len(self._in_vars)

        rem_grds = []
        var_set = set(self._in_vars)
        for gr in guards:
            params_pairs = dict(filter(lambda x: x[0] in gr.vars, varsym.items()))
            if not set(gr.vars) <= var_set:
                rem_grds.append(RRTransducer._guard_subs(gr, params_pairs))
                continue #too hard to decide now

            params = list(params_pairs.values())
            if not gr.pred(*params):
                return False, None
        return True, rem_grds


    @staticmethod
    def _cart_list_prod(l1, l2):
        ret = list()
        for i1 in l1:
            for i2 in l2:
                ret.append((i1, i2))
        return ret


    def _guard_symbol(self, varsym):
        grds = list()
        for var, val in varsym.items():
            grds.append(RRTGuardAct("= {0} {1}".format(var, val), [var], lambda x: x == val))
        return grds


    def _register_symbol(self, update, varsym):
        ret = list()
        for reg, up in update:
            if up in varsym:
                ret.append((reg, varsym[up]))
            else:
                ret.append((reg, up))
        return ret


    def product(self, nfa):
        inits = RRTransducer._cart_list_prod(self._init, list(nfa.Initial))
        finals = list()
        trans = dict()

        state_stack = list()
        state_stack = copy(inits)

        while state_stack:
            s1, s2 = state_stack.pop()
            if (s1 not in self._trans) or (s2 not in nfa.delta):
                continue
            for tr1 in self._trans[s1]:
                for sym, dst2_set in nfa.delta[s2].items():
                    varsym = dict(zip(self._in_vars, list(sym)))
                    sat, rm_grds = self._guard_sat(varsym, tr1.guard)
                    if not sat:
                        continue
                    rm_grds += self._guard_symbol(varsym)

                    if (s1,s2) not in trans:
                        trans[(s1, s2)] = list()
                    for dst2 in list(dst2_set):
                        trans[(s1, s2)].append(RRTTransition((s1, s2), \
                            rm_grds, self._register_symbol(tr1.tape_update, varsym),\
                            self._register_symbol(tr1.reg_update, varsym), \
                            (tr1.dest, dst2)))
                        state_stack.append((tr1.dest, dst2))
                        if (dst2 in nfa.Final) and (tr1.dest in self._fin):
                            finals.append((self._fin, dst2))

        return RRTransducer(self._name, self._in_vars, self._out_vars, \
            self._hist_regs, self._stack_regs, inits, finals, trans)
