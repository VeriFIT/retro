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


###########################################
if __name__ == '__main__':
    argc = len(sys.argv)
    if argc >= 3:
        fd_eq = open(sys.argv[1], "r")
        fd_aut = [open(sys.argv[i], "r") for i in range(2,argc) ]
    else:
        print("Invalid number of arguments: at least 2 are required")
        sys.exit(1)

    eq = parse_equations(fd_eq)
    nfa_eq = nfa_from_string(eq)
    nfa_sol = solution_nfa()
    ret = None

    trs = list(map (parse_rrt, fd_aut))
    rrts = list(map (autdict2RRTransducer, trs))
    all_nfa = copy(nfa_eq)

    while True:
        prods = [item.product(nfa_eq) for item in rrts]
        flatten = [item.flatten() for item in prods]

        curr_nfa = NFA()
        for rrt in flatten:
            rrt.rename_states()
            fado_aut = rrt.get_nfa()

            curr_nfa = curr_nfa.union(fado_aut)
            curr_nfa.elimEpsilon()

        curr_nfa = curr_nfa.minimal().toNFA()

        if (curr_nfa.conjunction(nfa_sol)).witness() != None:
            ret = True
            break

        all_nfa.Sigma = all_nfa.Sigma.union(curr_nfa.Sigma)
        test = all_nfa.conjunction(curr_nfa)
        if test.equivalentP(curr_nfa):
            ret = False
            break

        all_nfa = all_nfa.union(curr_nfa)
        all_nfa.elimEpsilon()
        nfa_eq = copy(curr_nfa)

    if ret:
        print("Sat")
    else:
        print("Unsat")

    for fd in fd_aut:
        fd.close()
    fd_eq.close()
