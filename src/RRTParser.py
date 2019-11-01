#!/usr/bin/env python3
# Parser of restricted register transducers in the VTF format

import collections

from RRTransducer import *
from VTFParser import parsevtf

Transition = collections.namedtuple("Transition",
                                    "src guard tape_update reg_update dst")


###########################################
def parse_parens(line):
    """Parses parenthesis block of a transition.

    :param line: [str]
    :return: (contents-of-parenthesis, rest-of-line)
    """
    orig_line = line
    if line[0] != '(':
        raise Exception("Expecting '(', got '{}' instead".format(line))

    line = line[1:]
    contents = list()
    while line and line[0] != ')':
        contents.append(line[0])
        line = line[1:]

    if not line:
        raise Exception("Error when parsing {}".format(orig_line))

    assert line[0] == ')'
    line = line[1:]
    return contents, line


###########################################
def parse_updates(lst_upd):
    """Parses tape and register updates.

    :param lst_upd: [str]
    :return: dict how tapes/registers should be updated
    """
    res = dict()
    for upd in lst_upd:
        words = upd.split('<-')
        if len(words) != 2:
            raise Exception("Invalid update: {}".format(upd))

        words = list(map(lambda x: x.strip(), words))
        if words[0] in res:
            raise Exception("A register cannot be updated more times: {}".format(words[0]))

        res[words[0]] = words[1]

    return res


###########################################
def parse_trans(line):
    """Parses a single line containing a transition.

    :param line: [str]
    :return: Transition
    """
    if not line:
        raise Exception("Passed empty line!")

    orig_line = line
    src = line[0]
    line = line[1:]

    guard, line = parse_parens(line)
    tape_update, line = parse_parens(line)
    tape_update = parse_updates(tape_update)
    reg_update, line = parse_parens(line)
    reg_update = parse_updates(reg_update)
    if len(line) != 1:
        raise Exception("Expecting destination state, received '{}'".format(line))

    dst = line[0]
    trans = Transition(src, guard, tape_update, reg_update, dst)
    return trans


###########################################
def parse_rrt(fd):
    """parse_rrt(fd) -> _|_

    Parses a restricted register transducer (RRT) file.

    :param: fd: file descriptor with the file
    :return: a RRT
    """
    parsed = parsevtf(fd)
    assert parsed.type == "RRT"

    aut = dict()
    aut["Name"] = parsed.dict["Name"]
    aut["Input-Track-Vars"] = parsed.dict["Input-Track-Vars"]
    aut["Output-Track-Vars"] = parsed.dict["Output-Track-Vars"]
    aut["History-Regs"] = parsed.dict["History-Regs"]
    aut["Stack-Regs"] = parsed.dict["Stack-Regs"]
    aut["Initial"] = parsed.dict["Initial"]
    aut["Final"] = parsed.dict["Final"]

    aut["Transitions"] = dict()
    for line in parsed.body:
        trans = parse_trans(line)
        if trans.src not in aut["Transitions"]:
            aut["Transitions"][trans.src] = list()

        assert trans.src in aut["Transitions"]
        aut["Transitions"][trans.src].append(trans)

    return aut


###########################################
def parse_guard(line):
    if line[0] == "(" and line[-1] == ")":
        line = line[1:-1]
        if line.startswith("="):
            vars = parse_vars(line[2:])
            return RRTGuardAct(line, vars, lambda x, y: x == y)
        if line.startswith("var"):
            vars = parse_vars(line[4:])
            return RRTGuardAct(line, vars, lambda x: x.isupper())
        if line.startswith("char"):
            vars = parse_vars(line[5:])
            return RRTGuardAct(line, vars, lambda x: x.islower())
        if line.startswith("isempty"):
            vars = parse_vars(line[8:])
            return RRTGuardAct(line, vars, lambda x: x == "")
        if line.startswith("isblank"):
            vars = parse_vars(line[8:])
            return RRTGuardAct(line, vars, lambda x: x == "?")
        if line.startswith("not"):
            rt = parse_guard(line[4:])
            return RRTGuardAct(line, rt.vars, lambda x: not rt.pred(x))
    else:
        raise Exception("Unexpected guard form. {0}".format(line))


###########################################
def parse_vars(line):
    return line.split()


###########################################
def autdict2RRTransducer(aut_dict):
    trans = dict()
    for key, lst in aut_dict["Transitions"].items():
        assert key not in trans
        #grds = map(parse_guard, value[1])
        trans[key] = list(map(lst2RRTTran, lst))
    return RRTransducer(aut_dict["Name"], aut_dict["Input-Track-Vars"], \
        aut_dict["Output-Track-Vars"], aut_dict["History-Regs"], \
        aut_dict["Stack-Regs"], aut_dict["Initial"], aut_dict["Final"], trans)


###########################################
def lst2RRTTran(value):
    grds = list(map(parse_guard, value[1]))
    return RRTTransition(value[0], grds, list(value[2].items()), list(value[3].items()), value[4])
