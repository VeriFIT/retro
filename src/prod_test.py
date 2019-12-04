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

def get_eq_items(smt_formula):
    wrap = SmtWrapper(smt_formula)
    vars = wrap.get_variables()
    var_dict = list(zip(vars, range(len(vars))))
    var_dict = dict(map(lambda x: (x[0], Symbol(1, x[1])), var_dict))
    is_len = False


    wrap.syntax_reduce()
    print(wrap.formulas)

    wrap.len_constr_rename_var(var_dict)
    pres_for = wrap.get_conj_pres_formula()

    len_constr_nfa = None
    if pres_for is not None:
        len_constr = pres_for.translate_to_nfa_vars(var_dict.values())
        len_constr_nfa = len_constr.nfa
        is_len = True

    eqs = wrap.get_str_equations_symbol(var_dict)
    raw_eq = wrap.get_str_equations(var_dict)
    nfa_eq = wrap.get_str_eq_automata(eqs, len_constr_nfa)
    str_nfa_eq = wrap.get_str_eq_automata(eqs)
    nfa_eq = nfa_eq.minimal().toNFA()
    nfa_eq.renameStates()
    return nfa_eq, var_dict, is_len, raw_eq, str_nfa_eq


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
            word = []
            word = trans_history[-1][1].prod_out_str(word)
            lengths = len_constr_word(word)
            model = get_model(word, lengths, trans_history[0:-1])
            return True, model

        all_nfa.Sigma = all_nfa.Sigma.union(curr_nfa.Sigma)
        comp = all_nfa.__invert__()
        comp.renameStates()
        if onthefly_empty_NFA(comp.toNFA(), curr_nfa):
            return False, None

        all_nfa.renameStates()
        all_nfa = disjoint_union(all_nfa.toNFA(), curr_nfa)
        all_nfa = all_nfa.toDFA()
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


def rmc_solve(nfa_eq, rrts, var_dict_rev, raw_eq):
    ret, model = rmc_loop_nfa(nfa_eq, rrts)
    if ret:
        ren_model = rename_model(model, var_dict_rev)
        print(ren_model)
        print("Model check: {0}".format(check_model(model, raw_eq)))
        print("Sat")
    else:
        print("Unsat")


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


def lst_starts_with(lst1, lst2):
    if len(lst1) > len(lst2):
        return False

    for i in range(len(lst1)):
        if lst1[i] != lst2[i]:
            return False
    return True


def count_sublist(lst1, lst2):
    n = len(lst1)
    cnt = 0
    ln = lst2
    for i in range(len(lst2)):
        if lst_starts_with(lst1, ln):
            cnt += 1
        ln = ln[1:]
    return cnt


def count_sublist_eqs(lst, eqs):
    cnt = 0
    for eq in eqs:
        cnt += count_sublist(lst, eq[0])
        cnt += count_sublist(lst, eq[1])
    return cnt


def get_vars_lst(lst):
    ret = set()
    for item in lst:
        if item.is_var():
            ret.add(item)
    return ret


def get_vars_eqs(eqs):
    vars = set()
    for eq in eqs:
        vars = vars | get_vars_lst(eq[0])
        vars = vars | get_vars_lst(eq[1])
    return vars


def replace_sublist(find, replace, lst):
    ret = list()
    n = len(find)
    i = 0
    while len(lst) > 0:
        if lst_starts_with(find, lst):
            lst = lst[n:]
            ret = ret + replace
        else:
            ret.append(lst[0])
            lst = lst[1:]
    return ret

def replace_sublist_eqs(find, replace, eqs):
    ret = list()
    for eq in eqs:
        ret.append((replace_sublist(find, replace, eq[0]), replace_sublist(find, replace, eq[1])))
    return ret


def replace_pairs_all(eqs):
    eqs_prev = None
    while eqs_prev != eqs:
        eqs_prev = eqs
        eqs = replace_pair(eqs)
    return eqs


def replace_pair(eqs):
    vars = get_vars_eqs(eqs)
    max_num = max(map(lambda x: x.val, vars))
    occur_dct = dict()
    for var in vars:
        occur_dct[var] = count_sublist_eqs([var], eqs)
    for var1 in vars:
        for var2 in vars:
            a = count_sublist_eqs([var1, var2], eqs)
            if (a == occur_dct[var1]) and (a == occur_dct[var2]):
                return replace_sublist_eqs([var1, var2], [Symbol(1, max_num+1)], eqs)
    return eqs


def replace_side_one(side, eqs, max_num):
    if len(side) < 3:
        return None
    a = count_sublist_eqs(side, eqs)
    if a > 1:
        ret = replace_sublist_eqs(side, [Symbol(1, max_num)], eqs)
        ret.append(([Symbol(1, max_num)], side))
        return ret
    return None


def replace_side(eqs):
    vars = get_vars_eqs(eqs)
    max_num = max(map(lambda x: x.val, vars)) + 1
    ret = eqs

    for eq in eqs:
        ret = replace_side_one(eq[0], eqs, max_num)
        if ret is not None:
            return ret
        ret = replace_side_one(eq[1], eqs, max_num)
        if ret is not None:
            return ret
    return eqs


def replace_side_all(eqs):
    eqs_prev = None
    while eqs_prev != eqs:
        eqs_prev = eqs
        eqs = replace_side(eqs)
    return eqs


def remove_simple_eqs(eqs):
    ret = eqs
    for eq in eqs:
        if (len(eq[0]) == 1) and (len(eq[1]) == 1):
            if count_sublist_eqs(eq[0], eqs) == 1:
                ret.remove(eq)
            elif count_sublist_eqs(eq[1], eqs) == 1:
                ret.remove(eq)
    return ret


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
    nfa_eq, var_dict, is_len, raw_eq, str_eq = get_eq_items(smt_for)
    var_dict_rev = dict([(v,k) for k, v in var_dict.items()])
    ret = None

    # print(raw_eq, get_vars_eqs(raw_eq))
    # repl_all = replace_side_all(raw_eq)
    # print(repl_all)
    # repl_pairs = replace_pairs_all(repl_all)
    # print(remove_simple_eqs(repl_pairs))
    #
    # for fd in fd_aut:
    #     fd.close()
    # fd_eq.close()
    # exit(0)

    trs = list(map (parse_rrt, fd_aut))
    rrts_all = list(map (autdict2RRTransducer, trs))

    if is_len:
        rrts = rrts_all[2:4]
        ret, _ = rmc_loop_nfa(str_eq, rrts)
        if not ret:
            print("Unsat")
        else:
            rrts = rrts_all[0:2]
            rmc_solve(nfa_eq, rrts, var_dict_rev, raw_eq)
    else:
        rrts = rrts_all[2:4]
        rmc_solve(nfa_eq, rrts, var_dict_rev, raw_eq)

    print("Time: {0}".format(round(time.time() - start_time, 2)))

    for fd in fd_aut:
        fd.close()
    fd_eq.close()
