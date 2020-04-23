#!/usr/bin/env python3

import automata.pyvata

from typing import Callable, List, Tuple, Dict
from FAdo.fa import *

from automata.LabelNFA import *
from automata.Symbol import *

class RRTGuardAct:
    # name: str
    # vars: List[str]
    # pred: Callable

    def __init__(self, nm, vr, pr):
        self.name = nm
        self.vars = vr
        self.pred = pr

    def __str__(self):
        return self.name


class RRTUpdateAct:
    def __init__(self, val, guard=None):
        self.val = val
        self.guard = guard

    def is_func(self):
        return (self.guard != None)

    def __str__(self):
        if self.is_func():
            return str(self.guard)
        else:
            return "@" + str(self.val)


class RRTTransition:
    # src: str
    # guard: List[RRTGuardAct]
    # tape_update: List[Tuple[str, str]]
    # reg_update: List[Tuple[str, str]]
    # dest: str
    # label: Tuple[str, str] = None

    def __init__(self, sr, gr, tp, rg, ds, lb = None):
        self.src = sr
        self.guard = gr
        self.tape_update = tp
        self.reg_update = rg
        self.dest = ds
        self.label = lb


class RRTransducer:

    def __init__(self, name, in_vars, out_vars, hist_regs, stack_regs, init, fin, trans, lab=None):
        self._name = name
        self._in_vars = in_vars
        self._out_vars = out_vars
        self._hist_regs = hist_regs
        self._stack_regs = stack_regs
        self._init = init
        self._fin = fin
        self._trans = trans
        self._label = lab

    def __str__(self):
        ret = "@RRT\n"
        ret = ret + "%Name {0}\n%Input-Track-Vars {1}\n%Output-Track-Vars {2}\n"\
            "%History-Regs {3}\n%Stack-Regs {4}\n%Initial {5}\n%Final {6}\n\n".\
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
                if tran.label:
                    ret = ret + "\t{0}\n".format(str(tran.label))
                ret = ret + "\t{0}\n\n".format(tran.dest)
        return ret


    ############################################################################
    @staticmethod
    def _guard_subs(guard, sub, varsk):
        name = guard.name
        #varsk = set(sub.keys())
        vars = [item for item in guard.vars if item not in varsk]
        # for var, sb in sub.items():
        #     name = name.replace(var, str(sb))
        pred = lambda *x: guard.pred(*RRTransducer._expand_guard_par(x, sub, guard.vars, vars))
        return RRTGuardAct(name, vars, pred)


    @staticmethod
    def _expand_guard_par(params, sub, vars_bef, vars_aft):
        dct = dict(zip(vars_aft, params))
        dct.update(sub)
        ret = [ dct[x] for x in vars_bef]
        return ret


    @staticmethod
    def _single_guard_sat(varsym, guard, varsym_keys=None):
        dec = True
        if varsym_keys is None:
            varsym_keys = set(varsym.keys())
        #params_pairs = {k:v for k, v in varsym.items() if k in guard.vars}
        params = list()
        params_pairs = dict()
        gr_vars = set(guard.vars)
        param_vars = set()

        for k, v in varsym.items():
            if k not in gr_vars:
                continue
            params_pairs[k] = v
            params.append(v)
            param_vars.add(k)

        #params_pairs = dict(filter(lambda x: x[0] in guard.vars, varsym.items()))
        if not gr_vars <= varsym_keys:
            rem_grds = RRTransducer._guard_subs(guard, params_pairs, param_vars)
            return None, rem_grds #too hard to decide now

        #params = list(params_pairs.values())
        return guard.pred(*params), None


    ############################################################################
    def _guard_sat(self, varsym, guards):
        rem_grds = []
        dec = True

        vars_set = set(varsym.keys())

        for gr in guards:
            dec, grd_add = RRTransducer._single_guard_sat(varsym, gr, vars_set)
            if dec is None:
                #return True, guards
                rem_grds.append(grd_add)
                continue
            if dec == False:
                return False, []
        return dec, rem_grds


    ############################################################################
    @staticmethod
    def _cart_list_prod(l1, l2):
        ret = list()
        for i1 in l1:
            for i2 in l2:
                ret.append((i1, i2))
        return ret


    ############################################################################
    @staticmethod
    def _guard_symbol(varsym):
        grds = list()
        for var, val in varsym.items():
            grds.append(RRTGuardAct("= {0} {1}".format(var, val), [var], lambda x: x == val))
        return grds


    ############################################################################
    @staticmethod
    def _register_symbol(update, varsym):
        ret = list()
        for reg, up in update:
            if up == "null":
                ret.append((reg, None))
            elif up == "eps":
                ret.append((reg, Symbol.epsilon()))
            elif up in varsym:
                ret.append((reg, varsym[up]))
            elif isinstance(up, RRTUpdateAct):
                dec, rem = RRTransducer._single_guard_sat(varsym, up.guard)
                if dec is None:
                    ret.append((reg, RRTUpdateAct(None, rem)))
                else:
                    ret.append((reg, dec))
            else:
                ret.append((reg, up))
        return ret

    ############################################################################
    def product_abstract(self, nfa_trans_dict, nfa_initials, nfa_finals):
        """
        Product (composition) of NFA in FAdo and RRT. Instantiate all input
        variables (with a possible guard-sat check) with values from the
        corresponding transition of NFA.
        """
        inits = RRTransducer._cart_list_prod(self._init, list(nfa_initials))
        finals = set()
        trans = dict()
        com_states = set(copy(inits))

        state_stack = list()
        state_stack = copy(inits)

        while state_stack:
            s1, s2 = state_stack.pop()

            tr1_all = None
            tr2_all = None
            try:
                tr1_all = self._trans[s1]
                tr2_all = nfa_trans_dict[s2].items()
            except KeyError:
                continue
            for tr1 in tr1_all:
                for sym, dst2_set in tr2_all:
                    lst = None
                    if isinstance(sym, tuple):
                        lst = list(sym)+[sym]
                    else:
                        lst = [sym]*len(self._in_vars)
                    varsym = dict(zip(self._in_vars, lst))
                    sat, rm_grds = self._guard_sat(varsym, tr1.guard)
                    if sat == False:
                        continue

                    for dst2 in list(dst2_set):
                        reg_upd = RRTransducer._register_symbol(tr1.reg_update, varsym)
                        new_tran = RRTTransition((s1, s2), \
                            rm_grds, RRTransducer._register_symbol(tr1.tape_update, varsym),\
                            reg_upd, \
                            (tr1.dest, dst2), sym)
                        try:
                            trans[(s1, s2)].append(new_tran)
                        except KeyError:
                            trans[(s1, s2)] = [new_tran]

                        dst_state = (tr1.dest, dst2)
                        if dst_state not in com_states:
                            com_states.add(dst_state)

                            state_stack.append(dst_state)
                            if (dst2 in nfa_finals) and (tr1.dest in self._fin):
                                finals.add(dst_state)

        return RRTransducer(self._name, self._in_vars, self._out_vars, \
            self._hist_regs, self._stack_regs, inits, list(finals), trans)


    def product_fado(self, nfa):
        return self.product_abstract(nfa.delta, nfa.Initial, nfa.Final)


    def product_vata(self, nfa):
        tr_dict = {}
        for tr in nfa.getTransitions():
            if tr[0] not in tr_dict:
                tr_dict[tr[0]] = { tr[1]: set([tr[2]]) }
            else:
                try:
                    tr_dict[tr[0]][tr[1]].add(tr[2])
                except KeyError:
                    tr_dict[tr[0]][tr[1]] = set([tr[2]])
        return self.product_abstract(tr_dict, nfa.getInitial(), nfa.getFinal())


    ############################################################################
    @staticmethod
    def _state_dict(state_dict, cnt, states):
        for st in states:
            if st not in state_dict:
                state_dict[st] = cnt
                cnt += 1
        return state_dict, cnt


    ############################################################################
    def rename_states(self):
        """
        Remove states (each state is a number -> begins with 0).
        """
        cnt = 0
        state_dict = dict()
        state_dict, cnt = RRTransducer._state_dict(state_dict, cnt, self._init)
        state_dict, cnt = RRTransducer._state_dict(state_dict, cnt, self._fin)
        trans = list()

        for src, tr_list in self._trans.items():
            tran_copy_list = list()
            for tr in tr_list:
                try:
                    src_ren = state_dict[src]
                except KeyError:
                    state_dict[src] = cnt
                    src_ren = cnt
                    cnt += 1
                try:
                    dest_ren = state_dict[tr.dest]
                except KeyError:
                    state_dict[tr.dest] = cnt
                    dest_ren = cnt
                    cnt += 1

                tran_copy = copy(tr)
                tran_copy.src = src_ren
                tran_copy.dest = dest_ren
                tran_copy_list.append(tran_copy)
            trans.append((src_ren, tran_copy_list))

        self._trans = dict(trans)
        self._init = list(map(lambda x: state_dict[x], self._init))
        self._fin = list(map(lambda x: state_dict[x], self._fin))


    ############################################################################
    def _regs_null(self):
        rt = list()
        for rg in self._hist_regs:
            rt.append((rg, None))
        for rg in self._stack_regs:
            rt.append((rg, None))
        return frozenset(rt)


    ############################################################################
    def flatten(self):
        """
        Remove registers and guards from composited RRT.
        """
        states = set()
        state_stack = list()
        trans = dict()
        label = dict()

        for ini in self._init:
            states.add((ini, self._regs_null()))

        state_stack = list(copy(states))
        inits = copy(state_stack)
        finals = set()


        while state_stack:
            s, regs = state_stack.pop()
            if s in self._fin:
                finals.add((s, regs))
            tr_all = None
            try:
                tr_all = self._trans[s]
            except KeyError:
                continue
            # if s not in self._trans:
            #     continue
            d = dict(regs)
            for tr in tr_all:
                varsym = copy(d)
                sat, rm_grds = self._guard_sat(varsym, tr.guard)
                if sat is None or len(rm_grds) > 0:
                    raise Exception("Guard with free variables")

                if sat == False:
                    continue

                tp_update = RRTransducer._register_symbol(tr.tape_update, varsym)
                varsym.update(dict(RRTransducer._register_symbol(tr.reg_update, varsym)))
                dest = (tr.dest, frozenset(varsym.items()))
                # if (s, regs) not in trans:
                #     trans[(s, regs)] = list()
                try:
                    trans[(s, regs)].append(RRTTransition((s, regs), [], tp_update, [], dest, tr.label))
                except KeyError:
                    trans[(s, regs)] = [RRTTransition((s, regs), [], tp_update, [], dest, tr.label)]
                if dest not in states:
                    state_stack.append(dest)
                    states.add(dest)

        return RRTransducer(self._name, self._in_vars, self._out_vars, \
            self._hist_regs, self._stack_regs, inits, list(finals), trans)


    def bad_state(self):
        for _,trs in self._trans.items():
            for tr in trs:
                if tr.src[0][0] == "bad" or tr.dest[0][0] == "bad":
                    return True
        return False


    ############################################################################
    def _symbol_from_tape(self, tape_update):
        """
        Create tuple symbol from transition tape update (assumes that each
        output variable is set).
        """
        lst = list()
        eps_cnt = 0
        no_eps = False
        for out in self._out_vars:
            try:
                sym = tape_update[out]
                if sym.is_eps():
                    eps_cnt = eps_cnt + 1
                else:
                    no_eps = True
                lst.append(sym)
            except KeyError:
                pass

        assert (eps_cnt == 0) or (eps_cnt > 0 and (not no_eps))

        if eps_cnt > 0:
            return Epsilon
        if len(lst) > 1:
            return tuple(lst)
        return lst[0]


    ############################################################################
    def prod_out_str(self, word):
        """
        Product output tape with a single word (return a word on the input tape).
        """
        inits = RRTransducer._cart_list_prod(self._init, [0])
        words = dict()
        com_states = set(copy(inits))

        state_stack = list()
        state_stack = copy(inits)

        for st in inits:
           words[st] = []

        while state_stack:
            s1, index = state_stack.pop()
            if (s1 in self._fin) and (index == len(word)):
                return words[(s1, index)]

            if s1 not in self._trans:
                continue
            for tr in self._trans[s1]:
                ind = None
                symbol = self._symbol_from_tape(dict(tr.tape_update))
                if symbol == Epsilon:
                    ind = index
                elif len(word) == 0:
                    continue
                elif index == len(word) or symbol != word[index]:
                    continue
                else:
                    ind = index + 1

                dst_state = (tr.dest, ind)
                if dst_state not in com_states:
                    com_states.add(dst_state)
                    state_stack.append(dst_state)
                    words[dst_state] = words[(s1, index)] + [tr.label]

        return None


    ############################################################################
    def get_nfa_fado(self):
        """
        Convert flattened RRT to NFA. Assumes numbered states (starting with 0).
        """

        ret = NFA()
        states = set(self._init)
        fins = set(self._fin)
        states = states | fins
        for src, tr_list in self._trans.items():
            for tr in tr_list:
                states.add(tr.src)
                states.add(tr.dest)
                ret.addTransition(tr.src, self._symbol_from_tape(dict(tr.tape_update)), tr.dest)
        for st in sorted(states):
            ret.addState(st)
        for fin in fins:
            ret.addFinal(fin)
        for ini in self._init:
            ret.addInitial(ini)
        return ret


    def get_nfa_vata(self):
        ret = automata.pyvata.NFA()
        fins = set(self._fin)
        for src, tr_list in self._trans.items():
            for tr in tr_list:
                ret.addTransition(tr.src, self._symbol_from_tape(dict(tr.tape_update)), tr.dest)
        for fin in fins:
            ret.addFinal(fin)
        for ini in self._init:
            ret.addInitial(ini)
        return ret


    ############################################################################
    def get_label_nfa(self):
        """
        Convert flattened RRT to Labelled NFA. Assumes numbered states (starting with 0).
        """

        ret = NFA()
        states = set(self._init)
        fins = set(self._fin)
        states = states | fins
        for src, tr_list in self._trans.items():
            for tr in tr_list:
                states.add(tr.src)
                states.add(tr.dest)
                ret.addTransition(tr.src, self._symbol_from_tape(dict(tr.tape_update)), tr.dest)
        for st in states:
            ret.addState(st)
        for fin in fins:
            ret.addFinal(fin)
        for ini in self._init:
            ret.addInitial(ini)
        return LabelNFA(ret, self._label)
