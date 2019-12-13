#!/usr/bin/env python3

import ast
from PresFormula import *
from SmtFormula import *
from itertools import chain
from collections import defaultdict
from Symbol import *
from AuxFunc import *
from Graph import *

conv_map = {EqFormulaType.LEQ: PresFormulaType.LEQ, \
    EqFormulaType.LE: PresFormulaType.LE, EqFormulaType.EQ: PresFormulaType.EQ}

class SmtWrapper:

    def __init__(self, fls):
        self.formulas = fls


    def get_pres_formulas(self):
        ret = list()
        for fl in self.formulas:
            if fl.is_constraint():
                ret.append(SmtWrapper.get_pres_formula(fl))
        return ret


    def get_conj_pres_formula(self):
        ret = list()
        for fl in self.formulas:
            if fl.is_constraint():
                ret.append(SmtWrapper.get_pres_formula(fl))
        if len(ret) == 0:
            return None
        if len(ret) == 1:
            return ret[0]

        fl = PresFormula(PresFormulaType.CONJ, ret[0:2])
        for i in range(2,len(ret)):
            fl = PresFormula(PresFormulaType.CONJ, [fl, ret[i]])
        return fl


    def get_variables(self):
        ret = set()
        for fl in self.formulas:
            if fl is not None:
                ret = ret | set(fl.get_variables())
        return ret


    @staticmethod
    def _create_dep_graph(chunks, raw_eqs):
        edges = list()
        n = len(chunks)
        for i in range(n):
            for sym in chunks[i]:
                for j in range(n):
                    if i == j:
                        continue
                    for left, right in raw_eqs[j]:
                        if sym in left or sym in right:
                            edges.append((i, j))
                            break
        return edges


    @staticmethod
    def _get_chunk_repr(left, right):
        side = None
        if any(isinstance(x, Symbol) for x in left):
            if any(isinstance(x, Symbol) for x in right):
                side = left
            else:
                side = right
        else:
            side = left
        return side


    def split_to_chunks(self):
        chunks = list()
        processed = list()
        processed_raw = list()
        fls = copy(self.formulas)
        for fl in self.formulas:
            if fl.is_str_equation():
                eq = fl.formulas[0]
                left, right = SmtWrapper._get_str_equation(eq)
                side = SmtWrapper._get_chunk_repr(left, right)

                if side in chunks:
                    i = chunks.index(side)
                    processed[i].append(fl)
                    processed_raw[i].append((left, right))
                else:
                    chunks.append(side)
                    processed.append([fl])
                    processed_raw.append([(left, right)])

        verts = list(range(len(chunks)))
        edges = SmtWrapper._create_dep_graph(chunks, processed_raw)
        graph = Graph(list(range(len(chunks))), edges)

        index_sort = graph.sort_dep_graph()
        processed_sort = list()
        for i in index_sort:
            processed_sort.append(processed[i])

        return processed_sort


    @staticmethod
    def _contain_chunk(chunk, raw):
        for symbol in chunk:
            for left, right in raw:
                if chunk != left and symbol in left:
                    return True
                if chunk != right and symbol in right:
                    return True
        return False


    @staticmethod
    def _chunk_index(side, chunks):
        index = 0
        for chunk in chunks:
            for symbol in side:
                if symbol in chunk:
                    return index
            index += 1
        return None




    @staticmethod
    def _get_side_atoms(smt_side):
        if smt_side.type == EqFormulaType.CONCAT:
            return SmtWrapper._get_side_atoms(smt_side.formulas[0]) + SmtWrapper._get_side_atoms(smt_side.formulas[1])
        elif smt_side.type == EqFormulaType.LITER:
            return [smt_side]
        elif smt_side.type == EqFormulaType.VAR:
            return [smt_side]
        raise Exception("Unexpected formula")


    def get_eqs_atoms(self):
        ret = list()
        for formula in self.formulas:
            if formula.is_str_equation():
                sides = formula.get_eq_sides()
                ret.append((SmtWrapper._get_side_atoms(sides[0]), SmtWrapper._get_side_atoms(sides[1])))
        return ret


    @staticmethod
    def _replace_pairs_all(eqs, max_num):
        eqs_prev = None
        while eqs_prev != eqs:
            eqs_prev = eqs
            eqs = SmtWrapper._replace_pair(eqs, max_num)
            max_num += 1
        return eqs


    @staticmethod
    def _create_new_var(num):
        return SmtFormula(EqFormulaType.VAR, [], "_tmp_{0}".format(num))


    @staticmethod
    def _get_var_from_atomlist(lst):
        return list(filter(lambda x: x.type == EqFormulaType.VAR, lst))


    @staticmethod
    def _get_var_from_eqs(eqs):
        ret = list()
        for eq in eqs:
            ret = ret + SmtWrapper._get_var_from_atomlist(eq[0])
            ret = ret + SmtWrapper._get_var_from_atomlist(eq[1])
        return remove_duplicates_lst(ret)


    @staticmethod
    def _replace_pair(eqs, max_num):
        occur_dct = dict()
        vars = SmtWrapper._get_var_from_eqs(eqs)
        for var in vars:
            occur_dct[var.value] = count_sublist_eqs([var], eqs)
        for var1 in vars:
            for var2 in vars:
                a = count_sublist_eqs([var1, var2], eqs)
                if (a == occur_dct[var1.value]) and (a == occur_dct[var2.value]):
                    return replace_sublist_eqs([var1, var2], [SmtWrapper._create_new_var(max_num)], eqs)
        return eqs


    @staticmethod
    def _replace_side_one(side, eqs, max_num):
        if len(side) < 3:
            return None
        a = count_sublist_eqs(side, eqs)
        if a > 1:
            ret = replace_sublist_eqs(side, [SmtWrapper._create_new_var(max_num)], eqs)
            ret.append(([SmtWrapper._create_new_var(max_num)], side))
            return ret
        return None


    @staticmethod
    def _replace_side(eqs, max_num):
        ret = eqs
        for eq in eqs:
            ret = SmtWrapper._replace_side_one(eq[0], eqs, max_num)
            if ret is not None:
                return ret
            ret = SmtWrapper._replace_side_one(eq[1], eqs, max_num)
            if ret is not None:
                return ret
        return eqs


    @staticmethod
    def _replace_side_all(eqs, max_num):
        eqs_prev = None
        while eqs_prev != eqs:
            eqs_prev = eqs
            eqs = SmtWrapper._replace_side(eqs, max_num)
            max_num += 1
        return eqs


    @staticmethod
    def _remove_simple_eqs(eqs):
        ret = eqs
        for eq in eqs:
            if (len(eq[0]) == 1) and (len(eq[1]) == 1) and \
                (eq[0][0].type == EqFormulaType.VAR) and (eq[1][0].type == EqFormulaType.VAR):
                if count_sublist_eqs(eq[0], eqs) == 1:
                    ret.remove(eq)
                elif count_sublist_eqs(eq[1], eqs) == 1:
                    ret.remove(eq)
        return ret


    def syntax_reduce(self):
        vars = self.get_variables()
        vars_n = len(vars) + 1
        eqs = self.get_eqs_atoms()
        eqs = SmtWrapper._replace_side_all(eqs, vars_n)
        max_n = vars_n + len(eqs)
        eqs = SmtWrapper._replace_pairs_all(eqs, max_n)
        eqs = SmtWrapper._remove_simple_eqs(eqs)

        vars = SmtWrapper._get_var_from_eqs(eqs)
        eqs = list(map(lambda x: SmtWrapper._atoms_smt_eq(x[0], x[1]), eqs))
        #decls = list(map(lambda x: SmtFormula(EqFormulaType.DECL, [x, None, SmtFormula(EqFormulaType.VAR, [], "String")]), vars))

        self.replace_str_eqs(eqs)
        #self.replace_var_decls(decls)


    def replace_var_decls(self, new_decls):
        ind = list()
        ret = list()
        for fl in self.formulas:
            if not fl.is_var_decl():
                ret.append(fl)
        self.formulas = [ret[0]] + new_decls + ret[1:]


    def replace_str_eqs(self, new_eqs):
        ind = list()
        ret = list()
        for fl in self.formulas:
            if not fl.is_str_equation():
                ret.append(fl)
        if len(ret) > 0:
            self.formulas = ret[0:-1] + new_eqs + [ret[-1]]
        else:
            self.formulas = new_eqs


    @staticmethod
    def _atoms_smt_side(side):

        if not isinstance(side, list):
            return side
        if len(side) == 1:
            return side[0]

        ret = SmtWrapper._atoms_smt_side(side[0:-1])
        at = SmtWrapper._atoms_smt_side(side[-1])
        return SmtFormula(EqFormulaType.CONCAT, [ret, at])


    @staticmethod
    def _atoms_smt_eq(left, right):
        l_smt = SmtWrapper._atoms_smt_side(left)
        r_smt = SmtWrapper._atoms_smt_side(right)
        return SmtFormula(EqFormulaType.ASSERT, [SmtFormula(EqFormulaType.EQ, [l_smt, r_smt])])


    def get_str_equations_symbol(self, var_dict):
        ret = list()
        for fl in self.formulas:
            if fl.is_str_equation():
                eq_smt = fl.formulas[0]
                assert eq_smt.type == EqFormulaType.EQ
                left = SmtWrapper.get_str_equation_symbols(eq_smt.formulas[0], var_dict)
                right = SmtWrapper.get_str_equation_symbols(eq_smt.formulas[1], var_dict)
                left, right = SmtWrapper.pad_equation(left, right)
                ret.append(list(zip(left, right)))
        return ret


    def get_str_equations(self, var_dict):
        ret = list()
        for fl in self.formulas:
            if fl.is_str_equation():
                left, right = SmtWrapper._get_str_equation(fl.formulas[0], var_dict)
                ret.append((left, right))
        return ret


    @staticmethod
    def _get_str_equation(smt_formula, var_dict=None):
        eq_smt = smt_formula
        assert eq_smt.type == EqFormulaType.EQ
        left = SmtWrapper.get_str_equation_symbols(eq_smt.formulas[0], var_dict)
        right = SmtWrapper.get_str_equation_symbols(eq_smt.formulas[1], var_dict)
        return left, right


    def get_str_eq_automata(self, eqs, len_constr=None):
        nfa = None
        n = len(eqs)
        for i in range(0, n):
            if i != 0:
                eqs[i].insert(0, (Symbol.delimiter(), Symbol.delimiter()))
            if nfa is not None:
                nfa = nfa.concat(SmtWrapper.nfa_from_string(eqs[i]))
            else:
                nfa = SmtWrapper.nfa_from_string(eqs[i])

        if len_constr is not None:
            delim = SmtWrapper.nfa_from_string([(Symbol.len_delim(), Symbol.len_delim())], False)
            nfa = nfa.concat(delim)
            nfa = nfa.concat(len_constr)
        return nfa


    def len_constr_rename_var(self, var_dict):
        for fl in self.formulas:
            if fl.is_constraint():
                fl.map_variables(lambda x: var_dict[x])


    @staticmethod
    def nfa_from_string(lst, sl=True):
        states = list(range(0,len(lst)))
        ret = NFA()
        i = 0
        for item in lst:
            ret.addState(i)
            ret.addTransition(i, item, i+1)
            i = i + 1
        ret.addState(i)
        if sl:
            ret.addTransition(i, (Symbol.blank(), Symbol.blank()), i)
        ret.addFinal(i)
        ret.addInitial(0)
        return ret



    @staticmethod
    def _pres_type_convert(type):
        return conv_map[type]


    @staticmethod
    def get_pres_formula(smt_formula):
        if smt_formula.type == EqFormulaType.ASSERT:
            assert len(smt_formula.formulas) == 1
            return SmtWrapper.get_pres_formula(smt_formula.formulas[0])
        if smt_formula.type in [EqFormulaType.LEQ, EqFormulaType.LE, EqFormulaType.EQ]:
            assert len(smt_formula.formulas) == 2
            a_dict = SmtWrapper.get_lin_vector(smt_formula.formulas[0])
            b_dict = SmtWrapper.get_lin_vector(smt_formula.formulas[1])
            return PresFormula(SmtWrapper._pres_type_convert(smt_formula.type), [], SmtWrapper.get_pres_triple(a_dict, b_dict))
        if smt_formula.type in [EqFormulaType.GEQ, EqFormulaType.GE]:
            assert len(smt_formula.formulas) == 2
            type = PresFormulaType.LE if smt_formula.type == EqFormulaType.GEQ else PresFormulaType.LEQ
            a_dict = SmtWrapper.get_lin_vector(smt_formula.formulas[0])
            b_dict = SmtWrapper.get_lin_vector(smt_formula.formulas[1])
            return PresFormula(PresFormulaType.NEG, [PresFormula(type, [], SmtWrapper.get_pres_triple(a_dict, b_dict))])


    @staticmethod
    def get_pres_triple(a_dict, b_dict):
        ret = defaultdict(int)
        for k, v in a_dict.items():
            ret[k] = v
        for k, v in b_dict.items():
            ret[k] = ret[k] - v

        b = -ret["_const_"]
        del ret["_const_"]
        lst = list(ret.items())
        vars = list(map(lambda x: x[0], lst))
        a_vec = list(map(lambda x: x[1], lst))
        return a_vec, vars, b


    @staticmethod
    def _plus_merge(a_dict, b_dict):
        ret = defaultdict(int)
        for k, v in chain(a_dict.items(), b_dict.items()):
            ret[k] += v
        return ret


    @staticmethod
    def _lin_mult_merge(a_dict, b_dict):
        assert len(a_dict) == 1 or len(b_dict) == 1
        dct = dict()
        mult = 1
        if len(a_dict) == 1 and "_const_" in a_dict:
            mult = a_dict["_const_"]
            dct = b_dict
        else:
            mult = b_dict["_const_"]
            dct = a_dict
        return {k: (mult*v) for k, v in dct.items()}


    @staticmethod
    def get_lin_vector(smt_formula):
        if smt_formula.type == EqFormulaType.CONST:
            return {"_const_": smt_formula.value}
        if smt_formula.type == EqFormulaType.VAR:
            return {smt_formula.value: int(1)}
        if smt_formula.type == EqFormulaType.MULT:
            assert len(smt_formula.formulas) == 2
            return SmtWrapper._lin_mult_merge(SmtWrapper.get_lin_vector(smt_formula.formulas[0]), \
                SmtWrapper.get_lin_vector(smt_formula.formulas[1]))
        if smt_formula.type == EqFormulaType.PLUS:
            assert len(smt_formula.formulas) == 2
            return SmtWrapper._plus_merge(SmtWrapper.get_lin_vector(smt_formula.formulas[0]), \
                SmtWrapper.get_lin_vector(smt_formula.formulas[1]))
        if smt_formula.type == EqFormulaType.LEN:
            assert len(smt_formula.formulas) == 1
            return SmtWrapper.get_lin_vector(smt_formula.formulas[0])
        raise Exception("Unsupported behaviour")


    @staticmethod
    def get_str_equation_symbols(smt_formula, var_dict=None):
        if smt_formula.type == EqFormulaType.CONCAT:
            assert len(smt_formula.formulas) == 2
            return SmtWrapper.get_str_equation_symbols(smt_formula.formulas[0], var_dict) + \
                SmtWrapper.get_str_equation_symbols(smt_formula.formulas[1], var_dict)
        if smt_formula.type == EqFormulaType.VAR:
            if var_dict is None:
                return [smt_formula.value]
            return [var_dict[smt_formula.value]]
        if smt_formula.type == EqFormulaType.LITER:
            str = ast.literal_eval("\"{0}\"".format(smt_formula.value))
            return list(map(lambda x: Symbol(False, ord(x)), str))
        raise Exception("Unsupported type of formula {0}".format(smt_formula))


    @staticmethod
    def pad_equation(left, right):
        diff = len(left) - len(right)
        if diff <= 0:
            left = left + abs(diff)*[Symbol.blank()]
        else:
            right = right + diff*[Symbol.blank()]
        return left, right
