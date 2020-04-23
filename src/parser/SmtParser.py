#!/usr/bin/env python3

from formula.SmtFormula import *

op_map = {"str.++": EqFormulaType.CONCAT, "str.len": EqFormulaType.LEN, \
    "=": EqFormulaType.EQ, "<": EqFormulaType.LE, "<=": EqFormulaType.LEQ, \
    ">": EqFormulaType.GE, ">=": EqFormulaType.GEQ, \
    "declare-fun": EqFormulaType.DECL, "assert": EqFormulaType.ASSERT, \
    "check-sat": EqFormulaType.CHECK, "set-logic": EqFormulaType.LOGIC_DECL,
    "*": EqFormulaType.MULT, "+": EqFormulaType.PLUS }

def get_name_token(line):
    line = line.strip()
    i = 0
    name = str()
    while (i < len(line)):
        if line[i].isspace() or line[i] == "(" or line[i] == ")":
            break
        name += line[i]
        i += 1
    return name, line[i:]


def get_op_type(name):
    return op_map[name]


def parse_atom_token(line):
    line = line.strip()
    n = len(line)
    atom = str()
    in_str = False
    i = 0

    while i < n:
        atom += line[i]
        if not in_str and line[i] == "\"":
            in_str = True
        elif in_str and line[i] == "\"":
            in_str = False
        if (not in_str) and (line[i].isspace()):
            return atom.strip(), line[i:]
        else:
            i += 1
    return atom.strip(), str()


def get_blocks(line):
    line = line.strip()
    blocks = list()
    block = str()

    while block is not None and (len(line) > 0):
        if line[0] != "(":
            block, line = parse_atom_token(line)
            blocks.append(block)
        else:
            block, line = get_single_block_brace(line)
            if block is not None:
                blocks.append(block)
        line = line.strip()
    return blocks



def get_single_block_brace(line):
    line = line.strip()
    if len(line) == 0:
        return None, None

    n = len(line)
    in_str = False
    cnt = 0
    for i in range(0, n):
        if not in_str and line[i] == "\"":
            in_str = True
        if in_str and line[i] == "\"":
            in_str = False
        if not in_str and line[i] == "(":
            cnt += 1
        elif not in_str and line[i] == ")":
            cnt -= 1
        if cnt == 0:
            return line[:i+1], line[i+1:]
    return None, None


def parse_single_atom(line):
    if line.startswith("\""):
        return EqFormulaType.LITER, line[1:-1]
    if line.isdigit() or (line[0] == "-" and line[1:].isdigit()):
        return EqFormulaType.CONST, int(line)
    else:
        return EqFormulaType.VAR, line


def parse_single_line(line):
    line = line.strip()
    if (line[0] != "(") or (line[-1] != ")"):
        type, val = parse_single_atom(line)
        return SmtFormula(type, [], val)

    line = line[1:-1]
    if len(line) == 0:
        return None

    token, line = get_name_token(line)
    type = get_op_type(token)
    formulas = list()
    for bl in get_blocks(line):
        formulas.append(parse_single_line(bl))
    return SmtFormula(type, formulas)


def parse_smt_file(fd):
    ret = list()
    content = fd.readlines()

    for line in content:
        ln = line.strip()
        if len(ln) != 0:
            ret.append(parse_single_line(ln))

    return ret
