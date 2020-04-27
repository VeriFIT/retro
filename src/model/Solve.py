#!/usr/bin/env python3

#from copy import deepcopy
#from FAdo.fa import *

#import RetroConfig
#import automata.RRTransducer
from automata.Symbol import *
#from automata.LabelNFA import *
#from automata.NFAOperation import *
#from parser.RRTParser import parse_rrt, autdict2RRTransducer
#from parser.EquationParser import parse_equations, nfa_from_string
#from parser.SmtParser import *
from model.ModelCons import *
from formula.SmtWrapper import *


class Solve:

    def __init__(self, rmc_loop):
        self._rmc_loop = rmc_loop


    @staticmethod
    def _get_eq_items(smt_formula, incl_len=True, syn_reduce=True):
        wrap = SmtWrapper(smt_formula)
        sat = None
        if syn_reduce:
            if not wrap.propagate_constants_check():
                sat = False
            wrap.syntax_reduce()
        vars = wrap.get_variables()
        var_dict = list(zip(vars, range(len(vars))))
        var_dict = dict(map(lambda x: (x[0], Symbol(1, x[1])), var_dict))
        is_len = False

        #wrap.len_constr_rename_var(var_dict)
        if incl_len:
            pres_for = wrap.get_conj_pres_formula(var_dict)
        else:
            pres_for = None

        len_constr_nfa = None
        if pres_for is not None:
            len_constr = pres_for.translate_to_nfa_vars(var_dict.values())
            len_constr_nfa = len_constr.nfa
            #len_constr_nfa = len_constr_nfa.minimal()
            is_len = True

        if wrap.contains_len_constr():
            is_len = True

        eqs = wrap.get_str_equations_symbol(var_dict)
        raw_eq = wrap.get_str_equations(var_dict)
        nfa_eq = wrap.get_str_eq_automata(eqs, len_constr_nfa)
        str_nfa_eq = wrap.get_str_eq_automata(eqs)
        nfa_eq = nfa_eq.minimal().toNFA()
        nfa_eq.renameStates()
        return nfa_eq, var_dict, is_len, raw_eq, str_nfa_eq, sat


    def iterative_solution(self, smt_lst, rrts):
        wrap = SmtWrapper(smt_lst)
        if wrap.light_unsat_check() == True:
            return False, None, None
        if not wrap.propagate_constants_check():
            return False, None, None
        if not wrap.propagate_constants_check():
            return False, None, None
        wrap.syntax_reduce()

        smt_lst = wrap.formulas
        smt_list_prime = smt_lst

        chunks = wrap.split_to_chunks()
        check_all = True
        model_all = dict()

        for i in range(len(chunks)):
            #print(i)
            ret, model, check = self._solve_smt(chunks[i], rrts)
            if not ret and i == 0:
                return False, None, None
            if not ret:
                return None, None, None
            model_all.update(model)
            check_all = check_all and check
            model = Solve._substitute_model(model)
            for fl in smt_list_prime:
                fl.substitute_vars(model)

        return True, model_all, check_all


    @staticmethod
    def _substitute_model(model):
        ret = dict()
        for key, val in model.items():
            item_str = str()
            for s in val:
                item_str += chr(s.val)
            item_str = item_str.replace('\n', '\\n')
            item_str = item_str.replace('\r', '\\r')
            item_str = item_str.replace('\v', '\\v')
            item_str = item_str.replace('\f', '\\f')
            ret[key] = item_str
        return ret


    @staticmethod
    def _rename_model(model, var_dict):
        return dict([(var_dict[k], v) for k, v in model.items()])



    def _rmc_solve_wrap(self, nfa_eq, rrts, var_dict_rev, raw_eq):
        ret, model = self._rmc_loop(nfa_eq, rrts)
        if ret:
            ren_model = Solve._rename_model(model, var_dict_rev)
            return ret, ren_model, ModelCons.check_model(model, raw_eq)
        else:
            return False, None, None


    def solution(self, rrts_all, smt_for):
        nfa_eq, var_dict, is_len, raw_eq, str_eq, sat = Solve._get_eq_items(smt_for, False)
        if sat == False:
            return False, None, None
        var_dict_rev = dict([(v,k) for k, v in var_dict.items()])
        ret = None
        if is_len:
            rrts = rrts_all[2:4]
            ret, _ = self._rmc_loop(str_eq, rrts)
            if not ret:
                return False, None, None
            else:
                nfa_eq, var_dict, is_len, raw_eq, str_eq, sat = Solve._get_eq_items(smt_for, True)
                if sat == False:
                    return False, None, None
                rrts = rrts_all[0:2]
                return self._rmc_solve_wrap(nfa_eq, rrts, var_dict_rev, raw_eq)
        else:
            rrts = rrts_all[2:4]
            return self._rmc_solve_wrap(nfa_eq, rrts, var_dict_rev, raw_eq)


    def _solve_smt(self, eqs_lst, rrts_all):
        nfa_eq, var_dict, is_len, raw_eq, str_eq, sat = Solve._get_eq_items(eqs_lst, True, False)
        if sat == False:
            return False, None, None
        var_dict_rev = dict([(v,k) for k, v in var_dict.items()])
        if is_len:
            rrts = rrts_all[2:4]
            ret, _ = self._rmc_loop(str_eq, rrts)
            if not ret:
                return ret, None, None
            else:
                rrts = rrts_all[0:2]
                ret, model = self._rmc_loop(nfa_eq, rrts)
                if ret:
                    ren_model = Solve._rename_model(model, var_dict_rev)
                    return ret, ren_model, ModelCons.check_model(model, raw_eq)
                return ret, None, None
        else:
            rrts = rrts_all[2:4]
            ret, model = self._rmc_loop(nfa_eq, rrts)
            if ret:
                ren_model = Solve._rename_model(model, var_dict_rev)
                return ret, ren_model, ModelCons.check_model(model, raw_eq)
            return ret, None, None
