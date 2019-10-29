#!/usr/bin/env python3

from dataclasses import dataclass
from typing import Callable, List, Tuple

@dataclass
class RRTGuardAct:
    name: str
    vars: List[str]
    pred: Callable

    def __str__(self):
        return self.name


@dataclass
class RRTTransition:
    src: str
    guard: List[RRTGuardAct]
    tape_update: List[Tuple[str, str]]
    reg_update: List[Tuple[str, str]]
    dest: str


class RRTransducer:

    def __init__(self, name, in_vars, out_vars, hist_regs, stack_regs, init, fin, trans):
        self._name = name
        self._in_vars = in_vars
        self._out_vars = out_vars
        self._hist_regs = hist_regs
        self._stack_regs = stack_regs
        self._init = init
        self._fin = fin
        self._trans = trans

    def __str__(self):
        ret = str()
        ret = ret + "Name: {0}\nInput-Track-Vars: {1}\nOutput-Track-Vars: {2}\n"\
            "History-Regs: {3}\nStack-Regs: {4}\nInitial: {5}\nFinal: {6}\n\n".\
            format(' '.join(map(str, self._name)), ' '.join(map(str, self._in_vars)), \
            ' '.join(map(str, self._out_vars)), ' '.join(map(str, self._hist_regs)), \
            ' '.join(map(str, self._stack_regs)), ' '.join(map(str, self._init)), \
            ' '.join(map(str, self._fin)))
        for _, trlist in self._trans.items():
            for tran in trlist:
                grn = list(map(str, tran.guard))
                ret = ret + tran.src + " ({0})\n".format(", ".join(grn))
                ret = ret + "\t({0})\n".format(", ".join(map((lambda x: "{0} <- {1}".format(x[0], x[1])), tran.tape_update)))
                ret = ret + "\t({0})\n".format(", ".join(map(lambda x: "{0} <- {1}".format(x[0], x[1]), tran.reg_update)))
                ret = ret + "\t{0}\n\n".format(tran.dest)
        return ret
