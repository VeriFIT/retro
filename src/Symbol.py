#!/usr/bin/env python3

import string
import copy as cp_mod

class Symbol:

    #type: 0-char, 1-var, 2-vector
    def __init__(self, typ, val):
        self.type = typ
        self.val = val


    def __str__(self):
        if self.is_var():
            return "V{0}".format(self.val)
        elif self.is_blank():
            return "_"
        elif self.is_delim():
            return "#"
        elif self.is_eps():
            return "eps"
        elif self.is_len_delim():
            return "@"
        elif self.is_symbol():
            if chr(self.val).isalnum():
                return chr(self.val)
            else:
                return "\\x{0}".format(self.val)
        else:
            return str(self.val)


    def __eq__(self, other):
        if isinstance(other, Symbol):
            return (self.type == other.type) and (self.val == other.val)
        return False

    def __le__(self, other):
        if (not self.type) and other.type:
            return True
        if self.type and (not other.type):
            return False
        return (self.val <= other.val)

    def __lt__(self, other):
        if (not self.type) and other.type:
            return True
        if self.type and (not other.type):
            return False
        return (self.val < other.val)


    def __hash__(self):
        return hash((self.val, self.type))


    def __repr__(self):
        return self.__str__()


    def proj(self, var):
        dct = dict(self.val)
        return Symbol(0, ord(str(dct[var])))


    def sub(self, var, val):
        ret = cp_mod.copy(self)
        dct = dict(ret.val)
        dct.update({var: val})
        ret.val = frozenset(dct.items())
        return ret


    def is_blank(self):
        return (not self.type) and (self.val == -1)


    def is_delim(self):
        return (not self.type) and (self.val == -2)


    def is_eps(self):
        return (not self.type) and (self.val == -3)


    def is_len_delim(self):
        return (not self.type) and (self.val == -4)


    def is_var(self):
        return (self.type == 1)


    def is_vector(self):
        return (self.type == 2)


    def is_symbol(self):
        return self.type == 0


    @staticmethod
    def blank():
        return Symbol(False, -1)


    @staticmethod
    def epsilon():
        return Symbol(False, -3)


    @staticmethod
    def delimiter():
        return Symbol(False, -2)
