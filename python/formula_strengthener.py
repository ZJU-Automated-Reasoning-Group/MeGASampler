from functools import reduce

from z3 import *
from interval import Interval, IntervalSet, INF, MINF, MININT, MAXINT
from z3_utils import *

import capnp

strengthen_capnp = capnp.load("strengthen.capnp")


class NoRuleForOp(Exception):
    def __init__(self, op_number, op_string, op_arity):
        self.op_arity = op_arity
        self.op_string = op_string
        self.op_number = op_number


class StrengthenedFormula():
    def __init__(self, debug=False, collect_unsimplified=False):
        self.collect_unsimplified = collect_unsimplified
        self.unsimplified_demands = []
        self.interval_set = IntervalSet.get_top()
        self.debug = debug

    def add_unsimplified_demand(self, demand):
        self.unsimplified_demands.append(demand)

    def __str__(self):
        return "Interval set: " + str(self.interval_set) + \
               "\nUnsimplified demands: " + str(self.unsimplified_demands)

    def __repr__(self):
        return str(self)

    def add_interval(self, var, interval):
        self.interval_set.add_interval(var, interval)

    def _strengthen_conjunct(self, conjunct, model):
        if is_bool(conjunct) and is_const(
                conjunct):  # case e=true/false/b/!b (where b is a boolean var)
            return  # ignore boolean literals, they are not part of the intervals
        elif is_not(conjunct):  # case Not(e)
            argument = conjunct.arg(0)
            if is_const(argument
                        ):  # case e=true/false/b/!b (where b is a boolean var)
                return  # ignore boolean literals, they are not part of the intervals
            else:
                neg_cond = negate_condition(argument)
                self._strengthen_conjunct(neg_cond, model)
        elif is_binary_boolean(conjunct):  # case (e bool_op c)
            lhs, rhs, lhs_value, rhs_value, op = evaluate_binary_expr(
                conjunct, model)
            # stren_binary_boolean expects op in >=,<=,==
            if op in Z3_DISTINCT_OPS:
                assert lhs_value != rhs_value
                conjunct = distinct_to_ineq(conjunct, lhs_value < rhs_value)
                op = get_op(conjunct)
            if op in Z3_LT_OPS or op in Z3_GT_OPS:
                op, rhs_value = self._strict_to_nonstrict(rhs_value, op)
            self._strengthen_binary_boolean_conjunct(lhs, lhs_value, rhs_value,
                                                     op, model)
        else:
            if self.collect_unsimplified:
                self.add_unsimplified_demand(conjunct)
            else:
                assert False, f"unexpected conjunct: {conjunct}"

    def _strict_to_nonstrict(self, rhs_value, op):
        if op in Z3_LT_OPS:
            return strict_to_nonstrict_bool_op(op), rhs_value - 1
        elif op in Z3_GT_OPS:
            return strict_to_nonstrict_bool_op(op), rhs_value + 1
        else:
            return op, rhs_value

    def _add_interval_for_binary_boolean(self, var, var_value, rhs_value, op):
        if op in Z3_LE_OPS:
            self.add_interval(var, Interval(MINF, rhs_value))
        elif op in Z3_LT_OPS:
            self.add_interval(var, Interval(MINF, rhs_value - 1))
        elif op in Z3_GE_OPS:
            self.add_interval(var, Interval(rhs_value, INF))
        elif op in Z3_GT_OPS:
            self.add_interval(var, Interval(rhs_value + 1, INF))
        elif op in Z3_EQ_OPS:
            self.add_interval(var, Interval(rhs_value, rhs_value))
        else:
            assert False

    @staticmethod
    def _replace_distinct_with_ineq(lhs, lhs_value, rhs_value):
        if lhs_value > rhs_value:
            return get_op(lhs > rhs_value)
        else:
            assert lhs_value < rhs_value
            return get_op(lhs < rhs_value)

    def _strengthen_mult(self, lhs_children, lhs_children_values, op,
                         rhs_value, model):
        lhs_value = math.prod(lhs_children_values)
        num_children = len(lhs_children)
        ge_op = op
        le_op = reverse_boolean_operator(op)
        if op in Z3_LE_OPS:
            le_op = op
            ge_op = reverse_boolean_operator(op)
        if (op in Z3_LE_OPS and lhs_value >= 0) or (op in Z3_GE_OPS
                                                    and lhs_value <= 0):
            i = 0
            while i < num_children:
                if lhs_children_values[i] >= 0:
                    self._strengthen_binary_boolean_conjunct(
                        lhs_children[i], lhs_children_values[i],
                        lhs_children_values[i], le_op, model)
                    self._strengthen_binary_boolean_conjunct(
                        lhs_children[i], lhs_children_values[i], 0, ge_op,
                        model)
                else:
                    self._strengthen_binary_boolean_conjunct(
                        lhs_children[i], lhs_children_values[i],
                        lhs_children_values[i], ge_op, model)
                    self._strengthen_binary_boolean_conjunct(
                        lhs_children[i], lhs_children_values[i], 0, le_op,
                        model)
                i = i + 1
        elif (op in Z3_LE_OPS and lhs_value <= 0) or (op in Z3_GE_OPS
                                                      and lhs_value >= 0):
            i = 0
            while i < num_children:
                if lhs_children_values[i] >= 0:
                    self._strengthen_binary_boolean_conjunct(
                        lhs_children[i], lhs_children_values[i],
                        lhs_children_values[i], ge_op, model)
                else:
                    self._strengthen_binary_boolean_conjunct(
                        lhs_children[i], lhs_children_values[i],
                        lhs_children_values[i], le_op, model)
                i = i + 1
        else:
            # todo raise exception
            print("warning: unexpected multiplication")

    def _strengthen_add(self, lhs_children, lhs_children_values, op, rhs_value,
                        model):
        constants = [c for c in lhs_children if is_numeral_constant(c)]
        if len(constants) > 0:
            non_constants = [
                c for c in lhs_children if not is_numeral_constant(c)
            ]
            non_constants_values = [
                lhs_children_values[i]
                for i in range(0, len(lhs_children_values))
                if not is_numeral_constant(lhs_children[i])
            ]
            constants_values = [
                lhs_children_values[i]
                for i in range(0,
                               len(lhs_children_values) - 1)
                if is_numeral_constant(lhs_children[i])
            ]
            diff = rhs_value - sum(constants_values)
            self._strengthen_add(non_constants, non_constants_values, op, diff,
                                 model)
            return
        num_children = len(lhs_children)
        if op in Z3_LE_OPS:
            lhs_value = sum(lhs_children_values)
            diff = rhs_value - lhs_value
            assert diff >= 0
            minimal_addition = diff // num_children
            extra_addition = diff - (minimal_addition * num_children)
            count_given_extra_addition = 0
            i = 0
            while count_given_extra_addition < extra_addition:
                value_i = lhs_children_values[i]
                self._strengthen_binary_boolean_conjunct(
                    lhs_children[i], value_i, value_i + minimal_addition + 1,
                    op, model)
                count_given_extra_addition += 1
                i += 1
            while i < num_children:
                value_i = lhs_children_values[i]
                self._strengthen_binary_boolean_conjunct(
                    lhs_children[i], value_i, value_i + minimal_addition, op,
                    model)
                i += 1
        elif op in Z3_GE_OPS:
            lhs_value = sum(lhs_children_values)
            diff = lhs_value - rhs_value
            assert diff >= 0, f"diff is {diff}, {lhs_children_values}"
            minimal_subtraction = diff // num_children
            extra_subtraction = diff - (minimal_subtraction * num_children)
            count_given_extra_subtraction = 0
            i = 0
            while count_given_extra_subtraction < extra_subtraction:
                value_i = lhs_children_values[i]
                self._strengthen_binary_boolean_conjunct(
                    lhs_children[i], value_i,
                    value_i - minimal_subtraction - 1, op, model)
                count_given_extra_subtraction += 1
                i += 1
            while i < num_children:
                value_i = lhs_children_values[i]
                self._strengthen_binary_boolean_conjunct(
                    lhs_children[i], value_i, value_i - minimal_subtraction,
                    op, model)
                i += 1
        else:
            pass  #todo raise exception

    def get_unsimplified_formula(self):
        return And(self.unsimplified_demands)

    def print_all_solutions(self, limit=100):
        if len(self.unsimplified_demands) == 0:
            return self.interval_set.print_all_values(limit)
        elif self.interval_set.is_top():
            return print_all_models(self.get_unsimplified_formula(), limit)
        else:
            print("Printing all solutions of mixed demands and intervals")
            interval_formula = self.interval_set.as_formula()
            f = And(interval_formula, self.get_unsimplified_formula())
            return print_all_models(f, limit)

    def _strengthen_mul_by_constant(self, constant, var_list, var_value_list,
                                    op, rhs_value, model):
        division_rounded_down = rhs_value // constant
        var_prod = reduce((lambda x, y: x * y), var_list)
        value_prod = math.prod(var_value_list)
        if constant > 0:
            should_round_up = (op in Z3_GE_OPS or op
                               in Z3_GT_OPS) and rhs_value % constant != 0
            self._strengthen_binary_boolean_conjunct(
                var_prod, value_prod, division_rounded_down + should_round_up,
                op, model)
        elif constant < 0:
            reversed_op = reverse_boolean_operator(op)
            should_round_up = (reversed_op in Z3_GE_OPS or reversed_op
                               in Z3_GT_OPS) and rhs_value % constant != 0
            self._strengthen_binary_boolean_conjunct(
                var_prod, value_prod, division_rounded_down + should_round_up,
                reversed_op, model)

    def _strengthen_binary_boolean_conjunct(self, lhs, lhs_value, rhs_value,
                                            op, model):
        assert op in Z3_GE_OPS or op in Z3_LE_OPS or op in Z3_EQ_OPS
        if self.debug:
            print("Strengthening: " + str(lhs) + " " + op_to_string(op) + " " +
                  str(rhs_value))
        if is_const(lhs):
            self._add_interval_for_binary_boolean(lhs, lhs_value, rhs_value,
                                                  op)
        elif op in Z3_EQ_OPS:
            children_values = get_children_values(lhs, model)
            for i in range(0, len(children_values)):
                if not is_numeral_constant(lhs.children()[i]):
                    self._strengthen_binary_boolean_conjunct(
                        lhs.children()[i], children_values[i],
                        children_values[i], op, model)
        elif is_app_of(lhs, Z3_OP_UMINUS):
            arg0 = lhs.arg(0)
            self._strengthen_binary_boolean_conjunct(
                arg0, -lhs_value, -rhs_value, reverse_boolean_operator(op),
                model)
        elif get_op(lhs) in Z3_ADD_OPS:
            children_values = get_children_values(lhs, model)
            self._strengthen_add(lhs.children(), children_values, op,
                                 rhs_value, model)
        elif get_op(lhs) in Z3_MUL_OPS:
            children_values = get_children_values(lhs, model)
            i = 0
            while i < len(lhs.children()):
                child = lhs.children()[i]
                if is_numeral_constant(child):
                    const_value = model_evaluate_to_const(child, model)
                    var_list = lhs.children()
                    var_list.pop(i)
                    children_values.pop(i)
                    self._strengthen_mul_by_constant(const_value, var_list,
                                                     children_values, op,
                                                     rhs_value, model)
                    return
                i = i + 1
            self._strengthen_mult(lhs.children(), children_values, op,
                                  rhs_value, model)
        elif is_binary(lhs):
            lhs_arg0, lhs_arg1, lhs_arg0_val, lhs_arg1_val, lhs_op = evaluate_binary_expr(
                lhs, model)
            if lhs_op in Z3_SUB_OPS:
                self._strengthen_add([lhs_arg0, -lhs_arg1],
                                     [lhs_arg0_val, -lhs_arg1_val], op,
                                     rhs_value, model)
            else:
                if self.collect_unsimplified:
                    print(
                        f"Unsupported binary operator: {op_to_string(lhs_op)}")
                    self.add_unsimplified_demand(
                        build_binary_expression(lhs, rhs_value, op))
                else:
                    raise NoRuleForOp(lhs_op, op_to_string(lhs_op), 2)
        else:
            lhs_op = get_op(lhs)
            if self.collect_unsimplified:
                print(
                    f"Unsupported non-binary operator: {op_to_string(lhs_op)}")
                self.add_unsimplified_demand(
                    build_binary_expression(lhs, rhs_value, op))
            else:
                raise NoRuleForOp(lhs_op, op_to_string(lhs_op),
                                  len(lhs.children))

    # A Strengthened formula is bottom iff its interval set is bottom
    # (i.e., contains an illegal interval like [3,2])
    def is_bottom(self):
        return self.interval_set.is_bottom()

    # A Strengthened formula is top iff its interval set is top
    # (i.e., contains no intervals) and it has no unsimplified demands
    def is_top(self):
        return self.interval_set.is_top() and len(
            self.unsimplified_demands) == 0

    # A Strengthened formula is bottom iff its interval set is bottom
    # (i.e., contains an illegal interval like [3,2])
    @staticmethod
    def get_bottom(debug=False):
        res = StrengthenedFormula(debug)
        res.interval_set = IntervalSet.get_bottom()
        return res

    # A Strengthened formula is top iff its interval set is top
    # (i.e., contains no intervals) and it has no unsimplified demands
    # This method is essentially the same as __init__, since init returns top
    @staticmethod
    def get_top(debug=False):
        return StrengthenedFormula(debug)

    # Modifies self to be the intersection of self and other.
    # Other is not modified
    def intersect(self, other):
        self.unsimplified_demands = self.unsimplified_demands + other.unsimplified_demands
        self.interval_set.intersect(other.interval_set)

    # Returns a new Strengthed formula instance which is the intersection of self and other.
    # Self and other are not modified
    @staticmethod
    def intersection(strengthened_formulas):
        res = StrengthenedFormula.get_top()
        for f in strengthened_formulas:
            res.intersect(f)
        return res

    def strengthen_and_add_condition(self, cond, model):
        strengthened_condition = strengthen(cond, model, self.debug)
        self.intersect(strengthened_condition)

    def substitute_var_with_expr(self, var, expr, model):
        self._substitute_var_in_demands(var, expr)
        if var not in self.interval_set:
            return
        else:
            var_interval = self.interval_set.get_interval(var)
            self.interval_set.delete_interval(var)
            if var_interval.is_high_inf():
                cond = var_interval.get_low_value() <= expr
            elif var_interval.is_low_minf():
                cond = expr <= var_interval.get_high_value()
            else:
                cond = And(var_interval.get_low_value() <= expr,
                           expr <= var_interval.get_high_value())
            self.strengthen_and_add_condition(cond, model)

    def _substitute_var_in_demands(self, var, expr):
        new_demands = []
        for demand in self.unsimplified_demands:
            new_demand = substitute(demand, [(var, expr)])
            new_demands.append(new_demand)
        self.unsimplified_demands = new_demands

    def __deepcopy__(self):
        return StrengthenedFormula.intersection(
            [self, StrengthenedFormula.get_top()])


def strengthen(f, model, debug=True):
    res = StrengthenedFormula(debug)
    f_as_and = nnf_simplify_and_remove_or(f, model)
    if debug:
        print("f_as_and: " + str(f_as_and))
    if get_op(f_as_and) in Z3_AND_OPS:
        # TODO: consider applying z3 propagate ineqs tactic here
        for c in f_as_and.children():
            res._strengthen_conjunct(c, model)
    else:  # f_is_and is an atomic boolean constraint
        res._strengthen_conjunct(f_as_and, model)
    return res


def nnf_simplify_and_remove_or(f, guiding_model):
    goal = Goal()
    goal.add(f)
    t_1 = Tactic('nnf')
    # nnf_formula = t_1(goal).as_expr()
    nnf_formula = Then(t_1, With('simplify', arith_lhs=True))(goal).as_expr()
    return And(remove_or(nnf_formula, guiding_model))


def nnf_simplify(f):
    goal = Goal()
    goal.add(f)
    t_1 = Tactic('nnf')
    nnf_formula = Then(t_1, With('simplify', arith_lhs=True))(goal).as_expr()
    return nnf_formula


def remove_or(nnf_formula, guiding_model):
    nnf_op = get_op(nnf_formula)
    # Every sub-formula that isn't an 'or' or an 'and' stops the recursion.
    # We assume conversion to nnf already removed other operators,
    # such as Implies, Ite, etc.
    if nnf_op not in Z3_OR_OPS and nnf_op not in Z3_AND_OPS:
        return [nnf_formula]
    # Step cases:
    if nnf_op in Z3_OR_OPS:
        for c in nnf_formula.children():
            if model_evaluate_to_const(c, guiding_model):
                # TODO: consider alternative heuristics for picking a clause
                return remove_or(c, guiding_model)
        assert False
    else:
        assert nnf_op in Z3_AND_OPS
        new_children = []
        for c in nnf_formula.children():
            new_children = new_children + remove_or(c, guiding_model)
        return new_children


def patch_z3_context(context_pointer):
    print(context_pointer)
    ctxobj = ContextObj(context_pointer)
    ctxobj.value = context_pointer  # why?!
    z3.main_ctx().ctx = ctxobj
    print(
        f"Patching the z3 global context, got {hex(context_pointer)}, {ctxobj}, {z3.main_ctx().ref()}"
    )


def strengthen_wrapper(f, model):
    ast = Ast(f)
    ast.value = f
    f = ExprRef(ast, z3.main_ctx())
    modelobj = ModelObj(model)
    modelobj.value = model
    model = ModelRef(modelobj, z3.main_ctx())

    b = strengthen_capnp.StrengthenResult.new_message()
    try:
        print(f"Calling strengthen with expr: {f}, model: {model}")
        res = strengthen(f, model)
    except NoRuleForOp as e:
        b.res = False
        b.failuredecription = f"Operator {e.op_string} ({e.op_number}) with arity {e.op_arity} found, " \
                              f" but there is no rule to handle it "
    else:
        b.res = True
        b.unsimplified = str(res.unsimplified_demands)
        b.init('intervalmap', len(res.interval_set.dict))
        for i, var in enumerate(res.interval_set.dict):
            capnpVarInterval = b.intervalmap[i]
            capnpVarInterval.variable = str(var)
            pythonInterval = res.interval_set.dict[var]
            capnpVarInterval.interval.islowminf = pythonInterval.is_low_minf()
            capnpVarInterval.interval.ishighinf = pythonInterval.is_high_inf()
            if pythonInterval.is_low_minf():
                capnpVarInterval.interval.low = MININT
            else:
                assert (isinstance(pythonInterval.low.n, int))
                capnpVarInterval.interval.low = pythonInterval.low.n
            if pythonInterval.is_high_inf():
                capnpVarInterval.interval.high = MAXINT
            else:
                assert (isinstance(pythonInterval.high.n, int))
                capnpVarInterval.interval.high = pythonInterval.high.n
    out = b.to_bytes()
    print(f"Result binary length: {len(out)}")
    # print(b)
    return out
