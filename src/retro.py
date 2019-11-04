#!/usr/bin/env python3
#
# TODO: some blah blah

import sys

import RRTransducer
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
    m.addTransition(0, ("X","a"), 1)
    m.addTransition(0, ("X","a"), 0)
    m.addTransition(0, ("c","c"), 3)
    m.addTransition(1, ("X","X"), 2)
    return m


def _automata_test():
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


###########################################
if __name__ == '__main__':
    argc = len(sys.argv)
    if argc == 3:
        fd_aut = open(sys.argv[1], "r")
        fd_eq = open(sys.argv[2], "r")
    else:
        print("Invalid number of arguments: 2 are required")
        sys.exit(1)

    tr = parse_rrt(fd_aut)
    rrt = autdict2RRTransducer(tr)

    eq = parse_equations(fd_eq)
    nfa_eq = nfa_from_string(eq)

    print("### RRT & NFA product ###")
    prod = rrt.product(nfa_eq)
    print(prod)

    fd_aut.close()
    fd_eq.close()
