#!/usr/bin/env python3

class ModelCons:

    def __init__(self, transducers):
        self._rrts = transducers


    @staticmethod
    def _get_string_tape(word):
        left = []
        right = []
        for ch in word:
            if not ch[0].is_blank():
                left.append(ch[0])
            if not ch[1].is_blank():
                right.append(ch[1])
        return left, right


    @staticmethod
    def _apply_rule(word, rule):
        after = []
        for ch in word:
            if ch == rule[0]:
                after.append(rule[1])
                after.append(rule[0])
            else:
                after.append(ch)
        return after


    @staticmethod
    def _apply_rule_eq(eq, rule):
        left = ModelCons._apply_rule(eq[0], rule)
        right = ModelCons._apply_rule(eq[1], rule)
        if left[0] == right[0]:
            return left[1:], right[1:]
        else:
            return left, right


    @staticmethod
    def _nielsen_rule(word1, word2, rule):
        before_flt = []

        for i in range(len(word2)):
            if word2[i][0] != word2[i][1]:
                before_flt = word2[i:]
                break
        before_fst = before_flt[0]

        if rule == 1:
            before_eq = ModelCons._get_string_tape(before_flt)
            after_eq = ModelCons._get_string_tape(word1)

            if before_fst[0].is_var() and before_fst[0] == word1[0][0] and ModelCons._apply_rule_eq(before_eq, (before_fst[0], before_fst[1])) == after_eq:
                return (before_fst[0], before_fst[1])
            if before_fst[1].is_var() and before_fst[1] == word1[0][1] and ModelCons._apply_rule_eq(before_eq, (before_fst[1], before_fst[0])) == after_eq:
                return (before_fst[1], before_fst[0])
            # if word1[0][0].is_blank() and word1[0][1].is_blank():
            #     return nielsen_rule(word1, word2, 0)
            # else:
            raise Exception("Non-matching word {0}; {1} -- {2}.".format(word1, word2, rule))
        if rule == 0:
            if before_fst[1].is_var() and before_fst[0] == word1[0][0]:
                return (before_fst[1], "Eps")
            if before_fst[0].is_var() and before_fst[1] == word1[0][1]:
                return (before_fst[0], "Eps")
            raise Exception("Non-matching word {0}, {1}.".format(word1, word2))


    def _get_rule(word, rrt_pair):
        image = rrt_pair[0].prod_out_str(word)
        if image is not None:
            return image, ModelCons._nielsen_rule(word, image, 1)

        image = rrt_pair[1].prod_out_str(word)
        if image is not None:
            return image, ModelCons._nielsen_rule(word, image, 0)
        return word, None


    def get_model(self, word):
        self._rrts.reverse()
        lengths = ModelCons._len_constr_word(word)
        rules = list()
        image = None
        for rrt_pair in self._rrts:
            image, rule = ModelCons._get_rule(word, rrt_pair)
            if rule is not None:
                rules.append(rule)
            word = image

        model = dict()
        if lengths is not None:
            for k, v in lengths.items():
                model[k] = ["X"]*v

        for rule in rules:
            if rule[1] == "Eps":
                model[rule[0]] = []
            else:
                if rule[1].is_var() and (rule[1] not in model):
                    model[rule[1]] = []
                if rule[1].is_var():
                    model[rule[0]] = model[rule[1]] + model[rule[0]]
                else:
                    model[rule[0]] = [rule[1]] + model[rule[0]]
        return model


    @staticmethod
    def _len_constr_word(word):
        n = len(word)
        len_constr = None
        for i in range(n):
            if isinstance(word[i], tuple) and word[i][0].is_len_delim() and word[i][1].is_len_delim():
                len_constr = word[i+1:]
                break
        if len_constr is None:
            return None

        vars = dict(len_constr[0].val).keys()
        base = 1
        res = dict([(v,0) for v in vars])
        for sym in len_constr:
            dct = dict(sym.val)
            for v in vars:
                res[v] += base*dct[v]
            base *= 2
        return res


    @staticmethod
    def _collect_eq_model(side, model):
        ret = list()
        for item in side:
            if item.is_var():
                try:
                    ret += model[item]
                except KeyError:
                    pass
            else:
                ret.append(item)
        return ret


    @staticmethod
    def check_model(model, raw_eq):
        for eq in raw_eq:
            left, right = eq
            if ModelCons._collect_eq_model(left, model) != ModelCons._collect_eq_model(right, model):
                return False
        return True
