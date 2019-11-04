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
        else:
            if chr(self.val).isalnum():
                return chr(self.val)
            else:
                return "\\x{0}".format(self.val)


    def __repr__(self):
        return self.__str__()


    def is_blank(self):
        return (not self.isvar) and (self.val == -1)


    def is_delim(self):
        return (not self.isvar) and (self.val == -2)


    @staticmethod
    def blank():
        return Symbol(False, -1)


    @staticmethod
    def delimiter():
        return Symbol(False, -2)
