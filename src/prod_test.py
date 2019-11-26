#!/usr/bin/env python3

import sys
import time

import RRTransducer
from Symbol import *
from LabelNFA import *
from NFAOperation import *
from RRTParser import parse_rrt, autdict2RRTransducer
from EquationParser import parse_equations, nfa_from_string
from SmtParser import *
from SmtWrapper import *

from FAdo.fa import *

def get_eq_nfa(smt_formula):
    wrap = SmtWrapper(smt_formula)
    vars = wrap.get_variables()
    var_dict = list(zip(vars, range(len(vars))))
    var_dict = dict(map(lambda x: (x[0], Symbol(1, x[1])), var_dict))

    wrap.len_constr_rename_var(var_dict)
    pres_for = wrap.get_conj_pres_formula()
    len_constr = pres_for.translate_to_nfa_vars(var_dict.values())

    eqs = wrap.get_str_equations(var_dict)
    nfa_eq = wrap.get_str_eq_automata(eqs, len_constr.nfa)
    nfa_eq = nfa_eq.minimal().toNFA()
    nfa_eq.renameStates()
    return nfa_eq


def rmc_loop_nfa(nfa_eq, rrts):
    all_nfa = copy(nfa_eq)
    trans_history = list()

    while True:
        prods = [item.product(nfa_eq.toNFA()) for item in rrts]
        flatten = list()
        for item in prods:
            flatten.append(item.flatten())

        curr_nfa = NFA()
        trans = list()
        for rrt in flatten:
            rrt.rename_states()
            trans.append(rrt)

            fado_aut = rrt.get_nfa().trim()
            fado_aut = fado_aut.minimal().trim().toNFA()
            fado_aut.renameStates()

            curr_nfa = disjoint_union(curr_nfa, fado_aut)

        trans_history.append(trans)

        if (curr_nfa.Initial & curr_nfa.Final) != set():
            word = [(Symbol.blank(), Symbol.blank())]
            print(get_model(word, trans_history))
            return True

        all_nfa.Sigma = all_nfa.Sigma.union(curr_nfa.Sigma)
        comp = all_nfa.__invert__()
        comp.renameStates()
        if onthefly_empty_NFA(comp.toNFA(), curr_nfa):
            return False

        all_nfa.renameStates()
        all_nfa = disjoint_union(all_nfa.toNFA(), curr_nfa)
        all_nfa = all_nfa.toDFA()
        nfa_eq = copy(curr_nfa)
        #nfa_eq = nfa_eq.trim()


def nielsen_rule(word1, word2, rule):
    fst2 = None
    for ch in word2:
        if ch[0] != ch[1]:
            fst2 = ch
            break

    if rule == 1:
        if fst2[0].is_var() and fst2[0] == word1[0][0]:
            return (fst2[0], fst2[1])
        if fst2[1].is_var() and fst2[1] == word1[0][1]:
            return (fst2[1], fst2[0])
        if word1[0][0].is_blank() and word1[0][1].is_blank():
            return nielsen_rule(word1, word2, 0)
        else:
            raise Exception("Non-matching word {0}; {1} -- {2}.".format(word1, word2, rule))
    if rule == 0:
        if fst2[1].is_var() and fst2[0] == word1[0][0]:
            return (fst2[1], "Eps")
        if fst2[0].is_var() and fst2[1] == word1[0][1]:
            return (fst2[0], "Eps")
        else:
            raise Exception("Non-matching word {0}, {1}.".format(word1, word2))


def get_rule(word, rrts):
    image = rrts[0].prod_out_str(word)
    if image is not None:
        return image, nielsen_rule(word, image, 1)

    image = rrts[1].prod_out_str(word)
    if image is not None:
        return image, nielsen_rule(word, image, 0)
    return word, None


def get_model(word, rrts):
    rrts.reverse()
    rules = list()
    image = None
    for rrt_pair in rrts:
        image, rule = get_rule(word, rrt_pair)
        if rule is not None:
            rules.append(rule)
        word = image

    print(word)
    model = dict()

    for rule in rules:
        if rule[1] == "Eps":
            model[rule[0]] = []
        else:
            if rule[1].is_var() and (rule[1] not in model):
                model[rule[1]] = []
            if rule[1].is_var():
                model[rule[0]] = model[rule[1]] + model[rule[0]]
            else:
                model[rule[0]] = [rule[1]] + model[rule[0]]
    return model


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
    if argc >= 3:
        fd_eq = open(sys.argv[1], "r")
        fd_aut = [open(sys.argv[i], "r") for i in range(2,argc) ]
    else:
        print("Invalid number of arguments: at least 2 are required")
        sys.exit(1)

    start_time = time.time()

    smt_for = parse_smt_file(fd_eq)
    nfa_eq = get_eq_nfa(smt_for)
    ret = None

    trs = list(map (parse_rrt, fd_aut))
    rrts = list(map (autdict2RRTransducer, trs))

    ret = rmc_loop_nfa(nfa_eq, rrts)
    if ret:
        print("Sat")
    else:
        print("Unsat")

    print("Time: {0}".format(round(time.time() - start_time, 2)))

    for fd in fd_aut:
        fd.close()
    fd_eq.close()


    # nfa_eq = parse_equations(fd_eq)
    # nfa_eq = nfa_eq.minimal().toNFA()
    #
    # trs = parse_rrt(fd_aut)
    # rrt = autdict2RRTransducer(trs)
    #
    # nfa = _tmp_nfa()
    #
    # print(rrt)
    #
    #
    # prod = rrt.product(nfa)
    # print(prod)
    #
    #
    # flat = prod.flatten()
    # flat.rename_states()
    # print(flat)
    #
    # aut = flat.get_nfa()
    # print(aut.dotFormat())


    # tr = parse_rrt(fd_aut)
    # rrt = autdict2RRTransducer(tr)
    #
    # smt_for = parse_smt_file(fd_eq)
    # nfa_eq = get_eq_nfa(smt_for)
    # print(nfa_eq.dotFormat())



    # rrt = rrt.product(nfa_eq)
    #
    # #print(rrt)
    #
    # flatten = rrt.flatten()
    # flatten.rename_states()
    #
    # #print(flatten)
    # fado_aut = flatten.get_nfa().trim()
    # fado_aut = fado_aut.minimal().trim().toNFA()
    # fado_aut.renameStates()
    #
    #
    # print(fado_aut.dotFormat())
    #
    # fd_aut.close()
    # fd_eq.close()
