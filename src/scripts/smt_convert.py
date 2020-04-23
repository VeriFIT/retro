#!/usr/bin/env python3

import sys
import time

import automata.RRTransducer
from automata.Symbol import *
from automata.LabelNFA import *
from automata.NFAOperation import *
from parser.RRTParser import parse_rrt, autdict2RRTransducer
from parser.EquationParser import parse_raw_equations
from parser.SmtParser import *
from formula.SmtWrapper import *
from formula.SmtFormula import *

from FAdo.fa import *

###########################################
if __name__ == '__main__':
    argc = len(sys.argv)
    if argc >= 2:
        fd_eq = open(sys.argv[1], "r")
    else:
        print("Invalid number of arguments: at least 2 are required")
        print("\t[smt file] [x-yx len] [x-eps len] [x-yx] [x-eps]")
        sys.exit(1)

    eqs = parse_raw_equations(fd_eq)
    eqs_smt = list()
    vars = set()
    for left, right in eqs:
        smt = SmtFormula.from_native_to_smt(left, right)
        vars = vars | set(smt.get_variables())
        eqs_smt.append(smt.to_smt_str())

    print("(set-logic QF_S)")
    for var in vars:
        print("(declare-fun {0} () String )".format(var))
    for smt_str in eqs_smt:
        print(smt_str.replace('\n', '\\n'))

    print("( check-sat )")

    fd_eq.close()
