#!/usr/bin/env python3
import collections
import functools
import sys

from VTFParser import parsevtf

RRTTransition = collections.namedtuple("RRTTransition",
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
def parse_rrt_trans(line):
    """Parses a single line containing a transition.

    :param line: [str]
    :return: RRTTransition
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
    trans = RRTTransition(src, guard, tape_update, reg_update, dst)
    return trans


###############################
def escape_str(s):
    """escape_str(str) -> str

Escapes a string for GraphViz dot tool.
"""
    s = s.replace('"', '\\"')

    return s


###########################################
def nfa_to_dot(nfa):
    """nfa_to_dot(NFA): _|_

    Transforms an NFA into the dot format.
    """
    ########################################
    state_map = dict()  #
    state_cnt = 0  #

    def get_state_id(name):  #
        nonlocal state_cnt  #
        if name not in state_map:  #
            state_map[name] = state_cnt  #
            state_cnt += 1  #
            #
        return str(state_map[name])  #

    ########################################

    print('Digraph G {\n')
    for trans in nfa.body:
        if len(trans) != 3:
            raise Exception('Invalid transition: ' + str(trans))

        str_trans = ''
        str_trans += get_state_id(trans[0])
        str_trans += ' -> '
        str_trans += get_state_id(trans[2])
        str_trans += ' [label="' + escape_str(trans[1]) + '"];'
        print(str_trans)

    init_cnt = 0
    for state in nfa.dict['Initial']:
        init_state_name = 'init' + str(init_cnt)
        init_cnt += 1

        str_init_state = ''
        str_init_state += init_state_name
        str_init_state += ' [label="",shape=plaintext];'
        print(str_init_state)

        str_init_trans = ''
        str_init_trans += init_state_name
        str_init_trans += ' -> '
        str_init_trans += get_state_id(state)
        str_init_trans += ';'
        print(str_init_trans)

    for state in state_map:
        str_state = ''
        str_state += get_state_id(state)
        str_state += ' [label="' + escape_str(state) + '"'

        if state in nfa.dict['Final']:
            str_state += ',peripheries=2'

        str_state += '];'
        print(str_state)

    print('}')


###########################################
def rrt2nfa(rrt):
    """rrt2nfa(rrt) -> NFA

    Transforms a Restricted Register Transducer (RRT) into an NFA (to be drawn,
    doesn't preserve semantics).
    """
    new_body = list()
    for trans in rrt.body:
        trans = parse_rrt_trans(trans)
        guard = functools.reduce(lambda x, y: x + " & " + y, trans.guard)
        item_to_asgn = lambda x: x[0] + " <- " + x[1]
        upd_list = list(map(item_to_asgn, trans.tape_update.items()))
        tape_upd = functools.reduce(lambda x, y: x + ", " + y, upd_list)
        upd_list = list(map(item_to_asgn, trans.reg_update.items()))
        reg_upd = functools.reduce(lambda x, y: x + ", " + y, upd_list)
        label = "{0}\\n{1}\\n{2}".format(guard, tape_upd, reg_upd)
        new_trans = (trans.src, label, trans.dst)
        new_body.append(new_trans)

    rrt.body = new_body
    return rrt


###########################################
def to_dot(fd):
    """to_dot(fd) -> _|_

    Transforms a VTF file into dot.
"""
    parsed = parsevtf(fd)

    if parsed.type == 'NFA':
        nfa_to_dot(parsed)
    if parsed.type == 'RRT':
        parsed = rrt2nfa(parsed)
        nfa_to_dot(parsed)
    return


###############################
if __name__ == '__main__':
    argc = len(sys.argv)
    if argc == 1:
        fd = sys.stdin
    elif argc == 2:
        fd = open(sys.argv[1], "r")
    else:
        print("Invalid number of arguments: either 0 or 1 required")
        sys.exit(1)

    to_dot(fd)
    if argc == 2:
        fd.close()
