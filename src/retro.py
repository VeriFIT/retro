#!/usr/bin/env python3
#
# TODO: some blah blah

import sys
import time

import RRTransducer
from Symbol import *
from NFAOperation import onthefly_empty
from RRTParser import parse_rrt, autdict2RRTransducer
from EquationParser import parse_equations, nfa_from_string

from FAdo.fa import *

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


def basic_cons_test(fado_aut):
    for f, to in fado_aut.delta.items():
        for sym, _ in to.items():
            if sym[0].is_delim():
                if not sym[1].is_delim():
                    print("Error {0}".format(sym))
                    fado_aut.renameStates()
                    print(fado_aut.dotFormat())
                    exit(1)
            if sym[1].is_delim():
                if not sym[0].is_delim():
                    print("Error {0}".format(sym))


def rmc_loop(nfa_eq, nfa_sol, rrts):
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

            curr_nfa = curr_nfa.union(fado_aut)

        curr_nfa = curr_nfa.toDFA()
        if curr_nfa.Initial in curr_nfa.Final:
            return True



        all_nfa.Sigma = all_nfa.Sigma.union(curr_nfa.Sigma)
        comp = all_nfa.__invert__().toDFA()
        comp.renameStates()
        if onthefly_empty(comp, curr_nfa):
            return False

        all_nfa = all_nfa.union(curr_nfa)
        nfa_eq = copy(curr_nfa)
        nfa_eq = nfa_eq.trim()



###########################################
if __name__ == '__main__':
    argc = len(sys.argv)
    if argc >= 3:
        fd_eq = open(sys.argv[1], "r")
        fd_aut = [open(sys.argv[i], "r") for i in range(2,argc) ]
    else:
        print("Invalid number of arguments: at least 2 are required")
        sys.exit(1)

    start_time = time.time()

    nfa_eq = parse_equations(fd_eq)
    nfa_eq = nfa_eq.minimal().toNFA()
    nfa_sol = solution_nfa()
    ret = None

    trs = list(map (parse_rrt, fd_aut))
    rrts = list(map (autdict2RRTransducer, trs))

    ret = rmc_loop(nfa_eq, nfa_sol, rrts)
    if ret:
        print("Sat")
    else:
        print("Unsat")

    print("Time: {0}".format(round(time.time() - start_time, 2)))

    for fd in fd_aut:
        fd.close()
    fd_eq.close()
