#include "strengthener.h"
#include <iostream>
#include <numeric>
#include <cmath>
#include "z3_utils.h"

void Strengthener::strengthen_literal(const z3::expr& literal){
  std::cout << "strengthening literal: " << literal.to_string() << "\n";
  assert(model_eval_to_bool(model, literal));
  if (literal.is_bool() && literal.is_const()){
    // case e=true/false/b/!b (where b is a boolean var)
    return; // TODO: this is what we do in Python. Is it correct?
  } else if (literal.is_not()){
    const z3::expr& argument = literal.arg(0);
    if (argument.is_const()){
      // case Not(true/false/b) (where b is a boolean var)
      return; // TODO: this is what we do in Python. Is it correct?
    } else {
      strengthen_literal(negate_condition(argument));
    }
  } else if (is_binary_boolean(literal)){
    const z3::expr& lhs = literal.arg(0);
    if (!lhs.is_int()) throw NoRuleForStrengthening();
    const z3::expr rhs = literal.arg(1);
    int64_t old_rhs_value;
    assert(rhs.is_numeral_i64(old_rhs_value));
    // turn op into >=,<=, or ==
    z3::expr literal_as_ineq(literal);
    if (literal.decl().decl_kind() == Z3_OP_DISTINCT){
      literal_as_ineq = lhs > rhs;
      if (model_eval_to_bool(model, lhs < rhs)){
        literal_as_ineq = lhs < rhs;
      }
    }
    if (is_lt(literal_as_ineq) || is_gt(literal_as_ineq)){
      literal_as_ineq = simplify_strict_to_nonstrict(literal_as_ineq);
    }
    int64_t lhs_value;
    int64_t rhs_value;
    assert(model.eval(literal_as_ineq.arg(0), true).is_numeral_i64(lhs_value));
    assert(model.eval(literal_as_ineq.arg(1), true).is_numeral_i64(rhs_value));
    auto op = get_op(literal_as_ineq);
    strengthen_binary_bool_literal(lhs, lhs_value, rhs_value, op);
  } else {
    throw NoRuleForStrengthening();
  }
}

void Strengthener::strengthen_binary_bool_literal(const z3::expr& lhs, int64_t lhs_value, int64_t rhs_value, Z3_decl_kind op){
  std::cout << "strengthening binary bool literal: " << lhs.to_string() << op_to_string(op) << rhs_value << "\n";
  assert (is_op_ge(op) or is_op_le(op) or is_op_eq(op));
  assert (lhs.is_int());
  if (is_numeral_constant(lhs)) return;
  if (lhs.is_const()){
    add_interval(lhs, rhs_value, op);
  } else if (is_op_eq(op)){
    for (unsigned int i=0; i<lhs.num_args(); i++){
      if (!is_numeral_constant(lhs.arg(i))){
        int64_t arg_value = model_eval_to_int64(model, lhs.arg(i));
        strengthen_binary_bool_literal(lhs.arg(i), arg_value, arg_value, op);
      }
    }
  } else {
    auto lhs_op = get_op(lhs);
    std::list<int64_t> arguments_values;
    get_arguments_values(lhs, model, arguments_values);
    if (is_op_uminus(lhs_op)) {
      std::cout << "strengthening unary minus: " << lhs.to_string() << op_to_string(op) << rhs_value << "\n";
      const z3::expr &arg0 = lhs.arg(0);
      strengthen_binary_bool_literal(arg0, -lhs_value, -rhs_value, reverse_bool_op(op));
    } else if (is_op_add(lhs_op)) {
      strengthen_add(lhs, lhs_value, arguments_values, op, rhs_value);
    } else if (is_op_mul(lhs_op)){
      strengthen_mult(lhs, lhs_value, arguments_values, op, rhs_value);
    } else if (is_op_sub(lhs_op)){
      strengthen_sub(lhs, arguments_values, op, rhs_value);
    } else {
      throw NoRuleForStrengthening();
    }
  }
}

void Strengthener::strengthen_mult(const z3::expr &lhs, int64_t lhs_value, std::list<int64_t>& arguments_values, Z3_decl_kind op,
                                   int64_t rhs_value) {
  std::cout << "strengthening mul: " << lhs.to_string() << op_to_string(op) << rhs_value << "\n";
  assert(arguments_values.size() == lhs.num_args());
  z3::expr non_constants_prod_e(c);
  int64_t constants_prod = 1;
  int64_t non_constants_prod = 1;
  int constants_count = 0;
  auto it = arguments_values.begin();
  for (unsigned int i=0; i<lhs.num_args(); i++){
    const z3::expr& argument = lhs.arg(i);
    int64_t value = *it;
    std::cout << "argument: " << argument.to_string() << " with value: " << value << "\n";
    if (is_numeral_constant(argument)){
      std::cout << "is numeral constant\n";
      constants_prod *= value; // TODO: safe computations
      constants_count++;
      it = arguments_values.erase(it);
    } else {
      std::cout << "is not a numeral constant\n";
      non_constants_prod *= value;
      if (non_constants_prod_e) {
        non_constants_prod_e = non_constants_prod_e * argument;
      } else {
        non_constants_prod_e = argument;
      }
      it++;
    }
  }
  if (constants_count > 0){
    strengthen_mult_by_constant(non_constants_prod_e, non_constants_prod, constants_prod, rhs_value, op);
  } else {
    strengthen_mult_without_constants(lhs, lhs_value, arguments_values, op, rhs_value);
  }
}

void Strengthener::strengthen_add(const z3::expr &lhs, int64_t lhs_value, std::list<int64_t> &arguments_values, Z3_decl_kind op,
                                  int64_t rhs_value) {
  std::cout << "strengthening add: " << lhs.to_string() << op_to_string(op) << rhs_value << "\n";
  assert(lhs.num_args() == arguments_values.size());
  z3::expr non_constants_sum_e(c);
  int64_t constants_sum = 0;
  int64_t non_constants_sum = 0;
  int constants_count = 0;
  auto it = arguments_values.begin();
  for (unsigned int i=0; i<lhs.num_args(); i++){
    const z3::expr& argument = lhs.arg(i);
    int64_t value = *it;
//    std::cout << "argument: " << argument.to_string() << " with value: " << value << "\n";
    if (is_numeral_constant(argument)){
//      std::cout << "is numeral constant\n";
      constants_sum += value; // TODO: safe computations
      constants_count++;
      it = arguments_values.erase(it);
    } else {
//      std::cout << "is not a numeral constant\n";
      non_constants_sum += value;
      if (non_constants_sum_e) {
        non_constants_sum_e = non_constants_sum_e + argument;
      } else {
        non_constants_sum_e = argument;
      }
      it++;
    }
  }
  if (constants_count > 0){
    strengthen_binary_bool_literal(non_constants_sum_e, non_constants_sum, rhs_value-constants_sum, op);
  } else {
    strengthen_add_without_constants(lhs, lhs_value, arguments_values, op, rhs_value);
  }
}

void Strengthener::add_interval(const z3::expr &lhs, int64_t rhs_value, Z3_decl_kind op) {
  std::cout << "adding interval: " << lhs.to_string() << op_to_string(op) << rhs_value << "\n";
  assert(lhs.is_const() || is_op_select(get_op(lhs)));
  if (is_op_ge(op)){
    i_map[lhs].set_lower_bound(rhs_value);
  } else if (is_op_le(op)){
    i_map[lhs].set_upper_bound(rhs_value);
  } else if (is_op_eq(op)){
    i_map[lhs].set_lower_bound(rhs_value);
    i_map[lhs].set_upper_bound(rhs_value);
  } else {
    throw NoRuleForStrengthening();
  }
}

void Strengthener::strengthen_sub(const z3::expr &lhs, std::list<int64_t> &arguments_values, Z3_decl_kind op,
                                  int64_t rhs_value) {
  std::cout << "strengthening subtraction: " << lhs.to_string() << op_to_string(op) << rhs_value << "\n";
  assert(arguments_values.size() == 2);
  int64_t second_arg_value = arguments_values.back();
  arguments_values.pop_back();
  int64_t first_arg_value = arguments_values.back();
  arguments_values.push_back(-second_arg_value);
  strengthen_add(lhs.arg(0) + (-lhs.arg(1)), first_arg_value-second_arg_value, arguments_values, op, rhs_value);
}

void Strengthener::strengthen_add_without_constants(const z3::expr &lhs, int64_t lhs_value, std::list<int64_t> &arguments_values,
                                                    Z3_decl_kind op, int64_t rhs_value) {
  assert(lhs.num_args() == arguments_values.size());
  unsigned int num_arguments = lhs.num_args();
  if (is_op_le(op)){
    int64_t diff = rhs_value - lhs_value;
    assert(diff >= 0);
    int64_t minimal_addition = std::floor((double)diff/num_arguments);
    int64_t extra_addition = diff - (minimal_addition * num_arguments);
    int count_given_extra_addition = 0;
    auto it = arguments_values.begin();
    unsigned int i = 0;
    while (count_given_extra_addition < extra_addition){
      assert(it!=arguments_values.end() && i<num_arguments);
      int64_t value_i = *it;
      strengthen_binary_bool_literal(lhs.arg(i), value_i, value_i + minimal_addition + 1, op);
      count_given_extra_addition ++;
      i++;
      it++;
    }
    while (i < num_arguments){
      assert(it!=arguments_values.end());
      int64_t value_i = *it;
      strengthen_binary_bool_literal(lhs.arg(i), value_i, value_i + minimal_addition, op);
      i++;
      it++;
    }
  } else if (is_op_ge(op)){
    int64_t diff = lhs_value - rhs_value;
    assert(diff >= 0);
    int64_t minimal_subtraction = std::floor((double)diff/num_arguments);
    int64_t extra_subtraction = diff - (minimal_subtraction * num_arguments);
    int count_given_extra_subtraction = 0;
    auto it = arguments_values.begin();
    unsigned int i = 0;
    while (count_given_extra_subtraction < extra_subtraction){
      assert(it!=arguments_values.end() && i<num_arguments);
      int64_t value_i = *it;
      strengthen_binary_bool_literal(lhs.arg(i), value_i, value_i - minimal_subtraction - 1, op);
      count_given_extra_subtraction++;
      i++;
      it++;
    }
    while (i < num_arguments){
      assert(it!=arguments_values.end());
      int64_t value_i = *it;
      strengthen_binary_bool_literal(lhs.arg(i), value_i, value_i - minimal_subtraction, op);
      i++;
      it++;
    }
  } else {
    throw NoRuleForStrengthening();
  }
}

void Strengthener::strengthen_mult_by_constant(const z3::expr &non_constant_arg, int64_t non_constant_arg_value,
                                               int64_t constant_value, int64_t rhs_value, Z3_decl_kind op) {
  std::cout << "strengthening multiply by constant: " << constant_value << "*" << non_constant_arg.to_string() <<
                                                        op_to_string(op) << rhs_value << "\n";
  int64_t division_rounded_down = std::floor((float)rhs_value / constant_value);
  if (constant_value > 0){
    bool should_round_up = (is_op_ge(op) or is_op_gt(op)) and rhs_value % constant_value != 0;
    strengthen_binary_bool_literal(non_constant_arg, non_constant_arg_value,
                                   division_rounded_down+should_round_up, op);
  } else if (constant_value < 0){
    Z3_decl_kind reversed_op = reverse_bool_op(op);
    bool should_round_up = (is_op_ge(reversed_op) or is_op_gt(reversed_op)) and rhs_value % constant_value != 0;
    strengthen_binary_bool_literal(non_constant_arg, non_constant_arg_value,
                                   division_rounded_down+should_round_up, reversed_op);
  } else {
    // case 0*expr op rhs, no need to add restrictions on expr
    return;
  }
}

void Strengthener::strengthen_mult_without_constants(const z3::expr &lhs, int64_t lhs_value, std::list<int64_t> &arguments_values,
                                                     Z3_decl_kind op, int64_t rhs_value) {
  std::cout << "strengthening multiply without constants: " << lhs.to_string() << op_to_string(op) << rhs_value << "\n";
  assert(lhs.num_args() == arguments_values.size());
  unsigned int num_arguments = lhs.num_args();
  Z3_decl_kind ge_op = op;
  Z3_decl_kind le_op = reverse_bool_op(op);
  if (is_op_le(op)){
    le_op = op;
    ge_op = reverse_bool_op(op);
  }
  if ((is_op_le(op) && lhs_value>=0) || (is_op_ge(op) && lhs_value<=0)) {
    auto it = arguments_values.begin();
    unsigned int i = 0;
    while (i < num_arguments) {
      assert(it != arguments_values.end());
      if (*it >= 0) {
        strengthen_binary_bool_literal(lhs.arg(i), *it, *it, le_op);
        strengthen_binary_bool_literal(lhs.arg(i), *it, 0, ge_op);
      } else {
        strengthen_binary_bool_literal(lhs.arg(i), *it, *it, ge_op);
        strengthen_binary_bool_literal(lhs.arg(i), *it, 0, le_op);
      }
      i++;
      it++;
    }
  } else if ((is_op_le(op) && lhs_value <= 0) || (is_op_ge(op) && lhs_value >= 0)){
    auto it = arguments_values.begin();
    unsigned int i = 0;
    while (i < num_arguments) {
      assert(it != arguments_values.end());
      if (*it >= 0) {
        strengthen_binary_bool_literal(lhs.arg(i), *it, *it, ge_op);
      } else {
        strengthen_binary_bool_literal(lhs.arg(i), *it, *it, le_op);
      }
      i++;
      it++;
    }
  } else {
    throw NoRuleForStrengthening();
  }
}

void Strengthener::print_interval_map() {
  std::cout << "interval map: ";
  for (auto const &pair: i_map) {
    std::cout << pair.first << ":" << pair.second << ",";
  }
  std::cout << "\n";
}