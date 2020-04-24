#!/usr/bin/env python3

import sys
import time

from copy import deepcopy

import RetroConfig
from parser.RRTParser import parse_rrt, autdict2RRTransducer
from parser.SmtParser import *
from model.Solve import *
from model.RMCLoop import *


###########################################
if __name__ == '__main__':
    argc = len(sys.argv)
    if argc >= 3:
        fd_eq = open(sys.argv[1], "r")
        fd_aut = [open(sys.argv[i], "r") for i in range(2,argc) ]
    else:
        print("Invalid number of arguments: at least 2 are required")
        print("\t[smt file] [x-yx len] [x-eps len] [x-yx] [x-eps]")
        sys.exit(1)

    start_time = time.time()

    smt_for = parse_smt_file(fd_eq)
    smt_for_copy = deepcopy(smt_for)
    smt_for_filter = copy(list(filter(lambda x: x.is_str_equation(), smt_for)))

    # nfa_eq, var_dict, is_len, raw_eq, str_eq = get_eq_items(smt_for, False)
    # var_dict_rev = dict([(v,k) for k, v in var_dict.items()])
    # ret = None

    trs = list(map (parse_rrt, fd_aut))
    rrts_all = list(map (autdict2RRTransducer, trs))

    solve = Solve(RMCLoop.rmc_loop_fado)

    model, check, sat = None, None, None
    #try:
    if RetroConfig.MULTI_EQ_OPTIMIZATION:
        sat, model, check = solve.iterative_solution(smt_for_filter, rrts_all)
    if sat is None:
        sat, model, check = solve.solution(rrts_all, smt_for_copy)
    if sat == True:
        print(model)
        print("Model check: {0}".format(check))
        print("sat")
    else:
        print("unsat")
    # except Exception:
    #     print("Not quadratic: {0}".format(sys.argv[1]))

    print("Time: {0}".format(round(time.time() - start_time, 2)))

    for fd in fd_aut:
        fd.close()
    fd_eq.close()
