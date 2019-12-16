
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


def onthefly_empty_no_invert_DFA(fa1, fa2):
    inits = RRTransducer._cart_list_prod([fa1.Initial], list(fa2.Initial))
    finals = set()
    trans = dict()
    com_states = set(copy(inits))

    state_stack = list()
    state_stack = copy(inits)

    while state_stack:
        s1, s2 = state_stack.pop()

        if (s2 in fa2.Final) and (s1 not in fa1.Final):
            return False

        if (s1 not in fa1.delta):
            return False
        if (s2 not in fa2.delta):
            continue

        for sym2, dst2_set in fa2.delta[s2].items():
            found = False
            for sym1, dst1 in fa1.delta[s1].items():
                if sym1 != sym2:
                    continue

                found = True
                for dst2 in dst2_set:
                    dst_state = (dst1, dst2)
                    if dst_state not in com_states:
                        com_states.add(dst_state)
                        state_stack.append(dst_state)
            if not found:
                return False
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


#Taken from FADO library
def toDFA(aut):
    aut.elimEpsilon()

    dfa = DFA()
    lStates = []
    sStates = set()
    stl = aut.Initial
    lStates.append(stl)
    sStates.add(frozenset(stl))
    dfa.setInitial(dfa.addState(stl))
    dfa.setSigma(aut.Sigma)
    for f in aut.Final:
        if f in stl:
            dfa.addFinal(0)
            break
    index = 0
    while True:
        slist = lStates[index]
        si = dfa.stateIndex(slist)
        for s, stl in get_succ_set(aut, slist, None).items():
            if not stl:
                continue
            if stl not in sStates:
                sStates.add(stl)
                lStates.append(stl)
                foo = dfa.addState(stl)
                for f in aut.Final:
                    if f in stl:
                        dfa.addFinal(foo)
                        break
            else:
                foo = dfa.stateIndex(stl)
            dfa.addTransition(si, s, foo)
        if index == len(lStates) - 1:
            break
        else:
            index += 1
    return dfa


def get_succ_set(aut, state_set, sym):
    res = set()
    ret = dict()
    for s in state_set:
        if s not in aut.delta:
            continue
        for sm, to in aut.delta[s].items():
            try:
                ret[sm] = ret[sm] | frozenset(to)
            except:
                ret[sm] = frozenset(to)
        # try:
        #     ls = aut.delta[s][sym]
        # except KeyError:
        #     ls = set()
        # except NameError:
        #     ls = set()
        # res = res | ls
    return ret
    #return frozenset(res)


#Taken from FADO library
def minimalBrzozowski(aut):
    return toDFA(toDFA(aut.reversal()).reversal())
