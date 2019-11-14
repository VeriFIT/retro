
from RRTransducer import *
from FAdo.fa import *

def onthefly_empty_DFA(fa1, fa2):
    inits = [(fa1.Initial, fa2.Initial)]
    finals = set()
    trans = dict()
    com_states = set(copy(inits))

    state_stack = list()
    state_stack = copy(inits)

    while state_stack:
        s1, s2 = state_stack.pop()

        if (s2 in fa2.Final) and (s1 in fa1.Final):
            return False

        if (s1 not in fa1.delta) or (s2 not in fa2.delta):
            continue
        for sym1, dst1 in fa1.delta[s1].items():
            for sym2, dst2 in fa2.delta[s2].items():
                if sym1 != sym2:
                    continue

                dst_state = (dst1, dst2)

                if dst_state not in com_states:
                    com_states.add(dst_state)
                    state_stack.append(dst_state)
    return True


def onthefly_empty_NFA(fa1, fa2):
    inits = RRTransducer._cart_list_prod(list(fa1.Initial), list(fa2.Initial))
    finals = set()
    trans = dict()
    com_states = set(copy(inits))

    state_stack = list()
    state_stack = copy(inits)

    while state_stack:
        s1, s2 = state_stack.pop()

        if (s2 in fa2.Final) and (s1 in fa1.Final):
            return False

        if (s1 not in fa1.delta) or (s2 not in fa2.delta):
            continue
        for sym1, dst1_set in fa1.delta[s1].items():
            for sym2, dst2_set in fa2.delta[s2].items():
                if sym1 != sym2:
                    continue

                for dst1 in dst1_set:
                    for dst2 in dst2_set:
                        dst_state = (dst1, dst2)
                        if dst_state not in com_states:
                            com_states.add(dst_state)
                            state_stack.append(dst_state)
    return True


def disjoint_union(fa1, fa2):
    nfa = fa1.dup()
    st_num = len(fa1.States)
    for st in range(st_num, st_num + len(fa2.States)):
        nfa.addState(st)
    for fn in fa2.Final:
        nfa.addFinal(fn+st_num)
    for ini in fa2.Initial:
        nfa.addInitial(ini+st_num)

    trans = dict()
    for src, dct in fa2.delta.items():
        for sym, dst_set in dct.items():
            for dst in dst_set:
                nfa.addTransition(src+st_num, sym, dst+st_num)
    return nfa


def contains_solution(nfa):
    inits = list(nfa.Initial)
    com_states = set(copy(inits))

    state_stack = list()
    state_stack = copy(inits)

    while state_stack:
        s = state_stack.pop()

        if (s in nfa.Final):
            return True

        if (s not in nfa.delta):
            continue
        for sym, dst_set in nfa.delta[s].items():
            if sym[0] != sym[1]:
                continue

            for dst in dst_set:
                if dst not in com_states:
                    com_states.add(dst)
                    state_stack.append(dst)
    return False
