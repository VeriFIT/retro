#!/usr/bin/env python3

import automata.RRTransducer
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
                # if rrt.bad_state():
                #     raise Exception("Not quadratic")

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

            # all_nfa.Sigma = all_nfa.Sigma.union(curr_nfa.Sigma)
            # comp = all_nfa.__invert__()
            # comp.renameStates()
            # if onthefly_empty_NFA(comp.toNFA(), curr_nfa):
            #     return False, None
            # all_nfa.Sigma = all_nfa.Sigma.union(curr_nfa.Sigma)
            # comp = all_nfa.__invert__()
            # comp.renameStates()
            all_nfa.renameStates()
            if onthefly_empty_no_invert_DFA(all_nfa, curr_nfa):
                return False, None

            #all_nfa.renameStates()
            all_nfa = disjoint_union(all_nfa.toNFA(), curr_nfa)
            all_nfa = toDFA(all_nfa)
            all_nfa = minimalBrzozowski(all_nfa)
            #all_nfa.renameStates()
            nfa_eq = copy(curr_nfa)
