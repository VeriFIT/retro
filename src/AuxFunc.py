

def lst_starts_with(lst1, lst2):
    if len(lst1) > len(lst2):
        return False

    for i in range(len(lst1)):
        if lst1[i] != lst2[i]:
            return False
    return True


def count_sublist(lst1, lst2):
    n = len(lst1)
    cnt = 0
    ln = lst2
    for i in range(len(lst2)):
        if lst_starts_with(lst1, ln):
            cnt += 1
        ln = ln[1:]
    return cnt


def count_sublist_eqs(lst, eqs):
    cnt = 0
    for eq in eqs:
        cnt += count_sublist(lst, eq[0])
        cnt += count_sublist(lst, eq[1])
    return cnt


def replace_sublist(find, replace, lst):
    ret = list()
    n = len(find)
    i = 0
    while len(lst) > 0:
        if lst_starts_with(find, lst):
            lst = lst[n:]
            ret = ret + replace
        else:
            ret.append(lst[0])
            lst = lst[1:]
    return ret


def replace_sublist_eqs(find, replace, eqs):
    ret = list()
    for eq in eqs:
        ret.append((replace_sublist(find, replace, eq[0]), replace_sublist(find, replace, eq[1])))
    return ret


def remove_duplicates_lst(lst):
    ret = list()
    for item in lst:
        if item not in ret:
            ret.append(item)
    return ret
