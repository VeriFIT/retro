#!/usr/bin/env python3

import sys
import time

import RetroConfig
import RRTransducer
from Symbol import *
from LabelNFA import *
from NFAOperation import *
from RRTParser import parse_rrt, autdict2RRTransducer
from EquationParser import parse_equations, nfa_from_string
from SmtParser import *
from SmtWrapper import *
from copy import deepcopy

from FAdo.fa import *

def get_eq_items(smt_formula, incl_len=True, syn_reduce=True):
    wrap = SmtWrapper(smt_formula)
    sat = None
    if syn_reduce:
        if not wrap.propagate_constants_check():
            sat = False
        wrap.syntax_reduce()
    vars = wrap.get_variables()
    var_dict = list(zip(vars, range(len(vars))))
    var_dict = dict(map(lambda x: (x[0], Symbol(1, x[1])), var_dict))
    is_len = False

    wrap.len_constr_rename_var(var_dict)
    if incl_len:
        pres_for = wrap.get_conj_pres_formula()
    else:
        pres_for = None

    len_constr_nfa = None
    if pres_for is not None:
        len_constr = pres_for.translate_to_nfa_vars(var_dict.values())
        len_constr_nfa = len_constr.nfa
        #len_constr_nfa = len_constr_nfa.minimal()
        is_len = True

    if wrap.contains_len_constr():
        is_len = True

    eqs = wrap.get_str_equations_symbol(var_dict)
    raw_eq = wrap.get_str_equations(var_dict)
    nfa_eq = wrap.get_str_eq_automata(eqs, len_constr_nfa)
    str_nfa_eq = wrap.get_str_eq_automata(eqs)
    nfa_eq = nfa_eq.minimal().toNFA()
    nfa_eq.renameStates()
    return nfa_eq, var_dict, is_len, raw_eq, str_nfa_eq, sat


def iterative_solution(smt_lst, rrts):
    wrap = SmtWrapper(smt_lst)
    if wrap.light_unsat_check() == True:
        return False, None, None
    if not wrap.propagate_constants_check():
        return False, None, None
    if not wrap.propagate_constants_check():
        return False, None, None
    wrap.syntax_reduce()

    smt_lst = wrap.formulas
    smt_list_prime = smt_lst

    chunks = wrap.split_to_chunks()
    check_all = True
    model_all = dict()

    for i in range(len(chunks)):
        #print(i)
        ret, model, check = solve_smt(chunks[i], rrts)
        if not ret and i == 0:
            return False, None, None
        if not ret:
            return None, None, None
        model_all.update(model)
        check_all = check_all and check
        model = substitute_model(model)
        for fl in smt_list_prime:
            fl.substitute_vars(model)

    return True, model_all, check_all


def substitute_model(model):
    ret = dict()
    for key, val in model.items():
        item_str = str()
        for s in val:
            item_str += chr(s.val)
        item_str = item_str.replace('\n', '\\n')
        item_str = item_str.replace('\r', '\\r')
        item_str = item_str.replace('\v', '\\v')
        item_str = item_str.replace('\f', '\\f')
        ret[key] = item_str
    return ret


def solve_smt(eqs_lst, rrts):
    nfa_eq, var_dict, is_len, raw_eq, str_eq, sat = get_eq_items(eqs_lst, True, False)
    if sat == False:
        return False, None, None
    var_dict_rev = dict([(v,k) for k, v in var_dict.items()])
    if is_len:
        rrts = rrts_all[2:4]
        ret, _ = rmc_loop_nfa(str_eq, rrts)
        if not ret:
            return ret, None, None
        else:
            rrts = rrts_all[0:2]
            ret, model = rmc_loop_nfa(nfa_eq, rrts)
            if ret:
                ren_model = rename_model(model, var_dict_rev)
                return ret, ren_model, check_model(model, raw_eq)
            return ret, None, None
    else:
        rrts = rrts_all[2:4]
        ret, model = rmc_loop_nfa(nfa_eq, rrts)
        if ret:
            ren_model = rename_model(model, var_dict_rev)
            return ret, ren_model, check_model(model, raw_eq)
        return ret, None, None


def len_constr_word(word):
    n = len(word)
    len_constr = None
    for i in range(n):
        if isinstance(word[i], tuple) and word[i][0].is_len_delim() and word[i][1].is_len_delim():
            len_constr = word[i+1:]
            break
    if len_constr is None:
        return None

    vars = dict(len_constr[0].val).keys()
    base = 1
    res = dict([(v,0) for v in vars])
    for sym in len_constr:
        dct = dict(sym.val)
        for v in vars:
            res[v] += base*dct[v]
        base *= 2
    return res


def collect_eq_model(side, model):
    ret = list()
    for item in side:
        if item.is_var():
            try:
                ret += model[item]
            except KeyError:
                pass
        else:
            ret.append(item)
    return ret



def check_model(model, raw_eq):
    for eq in raw_eq:
        left, right = eq
        if collect_eq_model(left, model) != collect_eq_model(right, model):
            return False
    return True



def rmc_loop_nfa(nfa_eq, rrts):
    all_nfa = copy(nfa_eq)
    all_nfa = all_nfa.toDFA()
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

            fado_aut = rrt.get_nfa()
            fado_aut.elimEpsilon().eliminateEpsilonTransitions()
            fado_aut = minimalBrzozowski(fado_aut).trim().toNFA()
            fado_aut.renameStates()

            curr_nfa = disjoint_union(curr_nfa, fado_aut)

        trans_history.append(trans)

        if (curr_nfa.Initial & curr_nfa.Final) != set():
            word = []
            word = trans_history[-1][1].prod_out_str(word)
            lengths = len_constr_word(word)
            model = get_model(word, lengths, trans_history[0:-1])
            return True, model

        # all_nfa.Sigma = all_nfa.Sigma.union(curr_nfa.Sigma)
        # comp = all_nfa.__invert__()
        # comp.renameStates()
        # if onthefly_empty_NFA(comp.toNFA(), curr_nfa):
        #     return False, None
        # all_nfa.Sigma = all_nfa.Sigma.union(curr_nfa.Sigma)
        # comp = all_nfa.__invert__()
        # comp.renameStates()
        all_nfa.renameStates()
        if onthefly_empty_no_invert_DFA(all_nfa, curr_nfa):
            return False, None

        #all_nfa.renameStates()
        all_nfa = disjoint_union(all_nfa.toNFA(), curr_nfa)
        all_nfa = toDFA(all_nfa)
        nfa_eq = copy(curr_nfa)


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


def rename_model(model, var_dict):
    return dict([(var_dict[k], v) for k, v in model.items()])


def get_model(word, lengths, rrts):
    rrts.reverse()
    rules = list()
    image = None
    for rrt_pair in rrts:
        image, rule = get_rule(word, rrt_pair)
        if rule is not None:
            rules.append(rule)
        word = image

    model = dict()
    if lengths is not None:
        for k, v in lengths.items():
            model[k] = ["X"]*v

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


def rmc_solve_wrap(nfa_eq, rrts, var_dict_rev, raw_eq):
    ret, model = rmc_loop_nfa(nfa_eq, rrts)
    if ret:
        ren_model = rename_model(model, var_dict_rev)
        return ret, ren_model, check_model(model, raw_eq)
    else:
        return False, None, None


def rmc_solve(rrts_all, smt_for):
    nfa_eq, var_dict, is_len, raw_eq, str_eq, sat = get_eq_items(smt_for, False)
    if sat == False:
        return False, None, None
    var_dict_rev = dict([(v,k) for k, v in var_dict.items()])
    ret = None
    if is_len:
        rrts = rrts_all[2:4]
        ret, _ = rmc_loop_nfa(str_eq, rrts)
        if not ret:
            return False, None, None
        else:
            nfa_eq, var_dict, is_len, raw_eq, str_eq, sat = get_eq_items(smt_for, True)
            if sat == False:
                return False, None, None
            rrts = rrts_all[0:2]
            return rmc_solve_wrap(nfa_eq, rrts, var_dict_rev, raw_eq)
    else:
        rrts = rrts_all[2:4]
        return rmc_solve_wrap(nfa_eq, rrts, var_dict_rev, raw_eq)



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

    model, check, sat = None, None, None
    if RetroConfig.MULTI_EQ_OPTIMIZATION:
        sat, model, check = iterative_solution(smt_for_filter, rrts_all)
    if sat is None:
        sat, model, check = rmc_solve(rrts_all, smt_for_copy)

    if sat == True:
        print(model)
        print("Model check: {0}".format(check))
        print("sat")
    else:
        print("unsat")

    print("Time: {0}".format(round(time.time() - start_time, 2)))

    for fd in fd_aut:
        fd.close()
    fd_eq.close()
