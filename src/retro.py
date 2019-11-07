#!/usr/bin/env python3
#
# TODO: some blah blah

import sys

import RRTransducer
from Symbol import *
from RRTParser import parse_rrt, autdict2RRTransducer
from EquationParser import parse_equations, nfa_from_string

from FAdo.fa import *
#from FAdo.reex import *
#from FAdo.fio import *

def _tmp_nfa():
    m = NFA()
    m.setSigma({("X","a"), ("b","X"), ("c","c")})
    m.addInitial(0)
    m.addState(0)
    m.addState(1)
    m.addState(2)
    m.addState(3)
    m.addFinal(1)
    m.addFinal(2)
    m.addTransition(0, Epsilon, 1)
    m.addTransition(0, ("X","a"), 0)
    m.addTransition(0, ("c","c"), 3)
    m.addTransition(1, ("X","X"), 2)
    return m


def _aut_test(rrt):
    aut = _tmp_nfa()

    print("### RRT & NFA product ###")
    prod = rrt.product(aut)
    print(prod)

    print("### Rename states ###")
    prod.rename_states()
    print(prod)

    print("### Removing registers ###")
    flatten = prod.flatten()
    print(flatten)

    print("### Rename states ###")
    flatten.rename_states()
    print(flatten)

    print("### FAdo NFA ###")
    nfa = flatten.get_nfa()
    print(nfa)

    print("### Minimal DFA ###")
    print(nfa.minimal())


def solution_nfa():
    ret = NFA()
    ret.addState(0)
    ret.addFinal(0)
    ret.addInitial(0)
    ret.addTransition(0, (Symbol.blank(), Symbol.blank()), 0)
    return ret


def onthefly_empty(fa1, fa2):
    inits = [(fa1.Initial, fa2.Initial)]
    finals = set()
    trans = dict()
    com_states = set(copy(inits))

    state_stack = list()
    state_stack = copy(inits)

    while state_stack:
        s1, s2 = state_stack.pop()

        if (s2 in fa2.Final) and (s1 in fa1.Final):
            return False

        if (s1 not in fa1.delta) or (s2 not in fa2.delta):
            continue
        for sym1, dst1 in fa1.delta[s1].items():
            for sym2, dst2 in fa2.delta[s2].items():
                if sym1 != sym2:
                    continue

                dst_state = (dst1, dst2)

                if dst_state not in com_states:
                    com_states.add(dst_state)
                    state_stack.append(dst_state)
    return True


###########################################
if __name__ == '__main__':
    argc = len(sys.argv)
    if argc >= 3:
        fd_eq = open(sys.argv[1], "r")
        fd_aut = [open(sys.argv[i], "r") for i in range(2,argc) ]
    else:
        print("Invalid number of arguments: at least 2 are required")
        sys.exit(1)

    nfa_eq = parse_equations(fd_eq)
    nfa_eq = nfa_eq.minimal().toNFA()

    nfa_sol = solution_nfa()
    ret = None

    trs = list(map (parse_rrt, fd_aut))
    rrts = list(map (autdict2RRTransducer, trs))
    all_nfa = copy(nfa_eq)

    while True:
        prods = [item.product(nfa_eq.toNFA()) for item in rrts]
        flatten = list()
        for item in prods:
            flatten.append(item.flatten())

        curr_nfa = NFA()
        for rrt in flatten:
            rrt.rename_states()
            fado_aut = rrt.get_nfa().trim()
            fado_aut = fado_aut.minimal().toNFA()

            # print("step")
            # print(rrt._name)
            # for f, to in fado_aut.delta.items():
            #     for sym, _ in to.items():
            #         if sym[0].is_delim():
            #             if not sym[1].is_delim():
            #                 print("Error {0}".format(sym))
            #                 fado_aut.renameStates()
            #                 print(fado_aut.dotFormat())
            #                 print(nfa_eq.dotFormat())
            #                 exit(1)
            #         if sym[1].is_delim():
            #             if not sym[0].is_delim():
            #                 print("Error {0}".format(sym))

            curr_nfa = curr_nfa.union(fado_aut)

        curr_nfa = curr_nfa.toDFA()
        if curr_nfa.Initial in curr_nfa.Final:
            ret = True
            break



        all_nfa.Sigma = all_nfa.Sigma.union(curr_nfa.Sigma)
        comp = all_nfa.__invert__().toDFA()
        comp.renameStates()
        if onthefly_empty(comp, curr_nfa):
            ret = False
            break

        all_nfa = all_nfa.union(curr_nfa)
        nfa_eq = copy(curr_nfa)
        nfa_eq = nfa_eq.trim()

    if ret:
        print("Sat")
    else:
        print("Unsat")

    for fd in fd_aut:
        fd.close()
    fd_eq.close()
