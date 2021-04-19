#!/usr/bin/env python3

import automata.RRTransducer
import automata.pyvata
from automata.Symbol import *
from automata.NFAOperation import *
from model.ModelCons import *

class RMCLoop:

    @staticmethod
    def rmc_loop_fado(nfa_eq, rrts):
        all_nfa = copy(nfa_eq)
        all_nfa = all_nfa.toDFA()
        trans_history = list()

        while True:
            prods = [item.product_fado(nfa_eq.toNFA()) for item in rrts]
            flatten = list()
            for item in prods:
                flatten.append(item.flatten())

            curr_nfa = NFA()
            trans = list()
            for rrt in flatten:
                if rrt.bad_state():
                    raise Exception("Not terminating")

                rrt.rename_states()
                trans.append(rrt)

                fado_aut = rrt.get_nfa_fado()
                fado_aut.elimEpsilon().eliminateEpsilonTransitions()
                fado_aut = minimalBrzozowski(fado_aut).trim().toNFA()
                fado_aut.renameStates()

                curr_nfa = disjoint_union(curr_nfa, fado_aut)

            trans_history.append(trans)

            if (curr_nfa.Initial & curr_nfa.Final) != set():
                word = []
                word = trans_history[-1][1].prod_out_str(word)
                model_con = ModelCons(trans_history[0:-1])
                model = model_con.get_model(word)
                return True, model

            all_nfa.renameStates()
            if onthefly_empty_no_invert_DFA(all_nfa, curr_nfa):
                return False, None

            all_nfa = disjoint_union(all_nfa.toNFA(), curr_nfa)
            all_nfa = toDFA(all_nfa)
            all_nfa = minimalBrzozowski(all_nfa)
            nfa_eq = copy(curr_nfa)


    @staticmethod
    def rmc_loop_vata(nfa_eq, rrts):
        nfa_eq = RMCLoop.fado_to_vata(nfa_eq.toNFA())

        all_nfa = copy(nfa_eq)

        trans_history = list()

        while True:
            prods = [item.product_vata(nfa_eq) for item in rrts]
            flatten = list()
            for item in prods:
                flatten.append(item.flatten())

            curr_nfa = automata.pyvata.NFA()
            trans = list()
            for rrt in flatten:
                rrt.rename_states()
                trans.append(rrt)

                vata_aut = rrt.get_nfa_vata()
                vata_aut = vata_aut.removeEpsilon(Epsilon)
                vata_aut = vata_aut.minimize()

                curr_nfa = automata.pyvata.NFA.union(curr_nfa, vata_aut)

            trans_history.append(trans)

            if curr_nfa.acceptsEpsilon():
                word = []
                word = trans_history[-1][1].prod_out_str(word)
                model_con = ModelCons(trans_history[0:-1])
                model = model_con.get_model(word)
                return True, model

            if automata.pyvata.NFA.isIncl(curr_nfa, all_nfa):
                return False, None

            all_nfa = automata.pyvata.NFA.union(all_nfa, curr_nfa)
            all_nfa = all_nfa.minimize()
            nfa_eq = copy(curr_nfa)


    @staticmethod
    def fado_to_vata(nfa):
        vata = automata.pyvata.NFA()
        for src, sym_dict in nfa.delta.items():
            for sym, dst_set in sym_dict.items():
                for dst in dst_set:
                    vata.addTransition(src, sym, dst)
        for i in nfa.Initial:
            vata.addInitial(i)
        for i in nfa.Final:
            vata.addFinal(i)
        return vata
