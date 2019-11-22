#!/usr/bin/env python3

import sys
import time

import RRTransducer
from Symbol import *
from LabelNFA import *
from NFAOperation import *
from RRTParser import parse_rrt, autdict2RRTransducer
from EquationParser import parse_equations, nfa_from_string

from FAdo.fa import *

def _tmp_nfa():
    m = NFA()
    #m.setSigma({("X","a"), ("b","X"), ("c","c")})
    x = Symbol(0, ord("X"))
    y = Symbol(0, ord("Y"))
    z = Symbol(0, ord("Z"))
    m.addInitial(0)
    m.addState(0)
    m.addState(5)
    m.addState(1)
    m.addState(2)
    m.addState(3)
    m.addState(4)
    m.addFinal(4)
    m.addTransition(0, (x, y), 5)
    m.addTransition(5, Symbol(2, frozenset([(x, 0), (y, 0), (z,1)])), 1)
    m.addTransition(1, Symbol(2,frozenset([(x, 0), (y, 1), (z,1)])), 2)
    m.addTransition(2, Symbol(2, frozenset([(x, 0), (y, 1), (z,1)])), 3)
    m.addTransition(3, Symbol(2, frozenset([(x, 1), (y, 0), (z,1)])), 4)
    return m


###########################################
if __name__ == '__main__':
    argc = len(sys.argv)
    if argc == 3:
        fd_eq = open(sys.argv[1], "r")
        fd_aut = open(sys.argv[2], "r")
    else:
        print("Invalid number of arguments: at least 2 are required")
        sys.exit(1)

    nfa_eq = parse_equations(fd_eq)
    nfa_eq = nfa_eq.minimal().toNFA()

    trs = parse_rrt(fd_aut)
    rrt = autdict2RRTransducer(trs)

    nfa = _tmp_nfa()

    print(rrt)


    prod = rrt.product(nfa)
    print(prod)


    flat = prod.flatten()
    flat.rename_states()
    print(flat)

    aut = flat.get_nfa()
    print(aut.dotFormat())



    fd_aut.close()
    fd_eq.close()
