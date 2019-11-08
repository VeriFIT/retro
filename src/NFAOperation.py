
from FAdo.fa import *

def onthefly_empty(fa1, fa2):
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
