#!/usr/bin/env python3
#
# TODO: some blah blah

import sys

import RRTransducer
from RRTParser import parse_rrt, autdict2RRTransducer

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
    m.addTransition(0, ("X","a"), 1)
    m.addTransition(0, ("c","c"), 3)
    m.addTransition(1, ("c","c"), 2)
    return m

###########################################
if __name__ == '__main__':
    argc = len(sys.argv)
    if argc == 1:
        fd = sys.stdin
    elif argc == 2:
        fd = open(sys.argv[1], "r")
    else:
        print("Invalid number of arguments: either 0 or 1 required")
        sys.exit(1)

    tr = parse_rrt(fd)
    rrt = autdict2RRTransducer(tr)
    print(rrt)

    aut = _tmp_nfa()
    #print(aut)

    prod = rrt.product(aut)
    print(prod)

    if argc == 2:
        fd.close()
