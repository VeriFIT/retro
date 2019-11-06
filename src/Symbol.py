#!/usr/bin/env python3

import string

class Symbol:

    def __init__(self, var, val):
        self.isvar = var
        self.val = val

    def __str__(self):
        if self.isvar:
            return "V{0}".format(self.val)
        elif self.is_blank():
            return "_"
        elif self.is_delim():
            return "#"
        elif self.is_eps():
            return "eps"
        else:
            if chr(self.val).isalnum():
                return chr(self.val)
            else:
                return "\\x{0}".format(self.val)


    def __eq__(self, other):
        if isinstance(other, Symbol):
            return (self.isvar == other.isvar) and (self.val == other.val)
        return False

    def __le__(self, other):
        if (not self.isvar) and other.isvar:
            return True
        if self.isvar and (not other.isvar):
            return False
        return (self.val <= other.val)

    def __lt__(self, other):
        if (not self.isvar) and other.isvar:
            return True
        if self.isvar and (not other.isvar):
            return False
        return (self.val < other.val)


    def __hash__(self):
        return hash((self.val, self.isvar))


    def __repr__(self):
        return self.__str__()


    def is_blank(self):
        return (not self.isvar) and (self.val == -1)


    def is_delim(self):
        return (not self.isvar) and (self.val == -2)


    def is_eps(self):
        return (not self.isvar) and (self.val == -3)


    @staticmethod
    def blank():
        return Symbol(False, -1)


    @staticmethod
    def epsilon():
        return Symbol(False, -3)


    @staticmethod
    def delimiter():
        return Symbol(False, -2)
