#!/usr/bin/env python3

import sys
import ast
import functools
import operator
from FAdo.fa import *
from Symbol import *


def split_symbols(line):
    state = 0
    ret = list()
    act = str()

    for s in line:
        if state == 0:
            if s.isspace():
                continue
            act = s
            if s == "\"":
                state = 1
            else:
                state = 2
        elif state == 1:
            act = act + s
            if s == "\"":
                state = 0
                ret.append(act)
        elif state == 2:
            if s.isspace():
                state = 0
                ret.append(act)
            else:
                act = act + s
    return ret


############################################################################
def divide_list(lst, delim):
    fst = list()
    snd = list()
    seen = False
    for l in lst:
        if l == delim:
            seen = True
            continue
        if seen:
            snd.append(l)
        else:
            fst.append(l)
    return fst, snd


############################################################################
def parse_single_equation(line):
    symbols = split_symbols(line)
    ll, rr = divide_list(symbols, "=")

    left = list(map(parse_symbol, ll))
    left_flat = functools.reduce(operator.iconcat, left, [])
    right = list(map(parse_symbol, rr))
    right_flat = functools.reduce(operator.iconcat, right, [])

    left_flat, right_flat = pad_equation(left_flat, right_flat)
    return list(zip(left_flat, right_flat))


############################################################################
def parse_raw_equations(fd):
    ret = list()
    nfa = None
    content = fd.readlines()

    for line in content:
        symbols = split_symbols(line)
        ll, rr = divide_list(symbols, "=")
        left = list(map(_parse_liter, ll))
        right = list(map(_parse_liter, rr))
        ret.append((left,right))
    return ret


def _parse_liter(atom):
    if atom.startswith("\""):
        return ast.literal_eval(atom)
    return atom


############################################################################
def parse_symbol(sym):
    if sym.startswith("V"):
        return [Symbol(True, int(sym[1:]))]
    if sym.startswith("\""):
        str = ast.literal_eval(sym)
        return list(map(lambda x: Symbol(False, ord(x)), str))
    raise Exception("Unexpected string token {0}".format(sym))


############################################################################
def pad_equation(left, right):
    diff = len(left) - len(right)
    if diff <= 0:
        left = left + abs(diff)*[Symbol.blank()]
    else:
        right = right + diff*[Symbol.blank()]
    return left, right


############################################################################
def parse_equations(fd):
    ret = list()
    nfa = None
    content = fd.readlines()

    for line in content:
        ret.append(parse_single_equation(line))

    ret = sorted(ret, key=len)
    ret.reverse()

    for i in range(0, len(ret)):
        if i != 0:
            ret[i].insert(0, (Symbol.delimiter(), Symbol.delimiter()))
        if nfa is not None:
            nfa = nfa.concat(nfa_from_string(ret[i]))
        else:
            nfa = nfa_from_string(ret[i])

    return nfa


############################################################################
def nfa_from_string(lst):
    states = list(range(0,len(lst)))
    ret = NFA()
    i = 0
    for item in lst:
        ret.addState(i)
        ret.addTransition(i, item, i+1)
        i = i + 1
    ret.addState(i)
    ret.addTransition(i, (Symbol.blank(), Symbol.blank()), i)
    ret.addFinal(i)
    ret.addInitial(0)
    return ret
