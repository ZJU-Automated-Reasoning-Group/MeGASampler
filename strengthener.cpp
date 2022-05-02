#include "strengthener.h"
#include <iostream>
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
      strengthen_add(lhs, arguments_values, op, rhs_value);
    } else if (is_op_mul(lhs_op)){
      strengthen_mult(lhs, arguments_values, op, rhs_value);
    } else if (is_op_sub(lhs_op)){
      strengthen_sub(lhs, arguments_values, op, rhs_value);
    } else {
      throw NoRuleForStrengthening();
    }
  }
}

void Strengthener::strengthen_mult(const z3::expr &lhs, std::list<int64_t>& arguments_values, Z3_decl_kind op,
                                   int64_t rhs_value) {
  std::cout << "strengthening mul: " << lhs.to_string() << op_to_string(op) << rhs_value << "\n";
  //TODO: finish
  unsigned int i=0;
  while (i < lhs.num_args()){
    const z3::expr& child = lhs.arg(i);
    if (is_numeral_constant(child)){
      int64_t child_value = model_eval_to_int64(model, child);
    }
    i++;
  }
//      var_list = lhs.children()
//      var_list.pop(i)
//      children_values.pop(i)
//      self._strengthen_mul_by_constant(const_value, var_list,
//                                       children_values, op,
//                                       rhs_value, model)
//      return
//              i = i + 1
//      self._strengthen_mult(lhs.children(), children_values, op,
//                            rhs_value, model)
}

void Strengthener::strengthen_add(const z3::expr &lhs, std::list<int64_t> &arguments_values, Z3_decl_kind op,
                                  int64_t rhs_value) {
  std::cout << "strengthening add: " << lhs.to_string() << op_to_string(op) << rhs_value << "\n";
  //TODO: implement
}

void Strengthener::add_interval(const z3::expr &lhs, int64_t rhs_value, Z3_decl_kind op) {
  std::cout << "adding interval: " << lhs.to_string() << op_to_string(op) << rhs_value << "\n";
  //TODO: implement
}

void Strengthener::strengthen_sub(const z3::expr &lhs, std::list<int64_t> &arguments_values, Z3_decl_kind op,
                                  int64_t rhs_value) {
  std::cout << "strengthening subtraction: " << lhs.to_string() << op_to_string(op) << rhs_value << "\n";
  assert(arguments_values.size() == 2);
  int64_t second_arg_value = arguments_values.back();
  arguments_values.pop_back();
  arguments_values.push_back(-second_arg_value);
  strengthen_add(lhs.arg(0) + (-lhs.arg(1)), arguments_values, op, rhs_value);
}

int main() {
  std::cout << "Hello strengthener!!\n";
  z3::context c;
  z3::expr x = c.int_const("x");
  z3::expr y = c.int_const("y");
  z3::expr z = c.int_const("z");
  z3::expr b1 = c.bool_const("b1");
  z3::expr b2 = c.bool_const("b2");
//  z3::expr f = b1 == b2; // NoRuleForStrengthening
//  z3::expr f = x*y*z > 5; // NoRuleForStrengthening
//  z3::expr f = (!(x != 5)); // should work
//  z3::expr f = (x*y)-z < 9; // should work
//  z3::expr f = !((x*y)-z < 9); // should work
//  z3::expr f = !((x*0)-z <= 9); // should work
//  z3::expr f = b1; // should work
//  z3::expr f = !b2; // should work
//  z3::expr f = 3*(x+4) != 20; // should work
  z3::expr f = 3*(x+4) != x; // assertion failure - rhs is not a number
//  z3::expr f = (x+y)*z > 5; // should work
  z3::solver solver(c);
  solver.add(f);
  auto res = solver.check();
  assert(res == z3::sat);
  z3::model m = solver.get_model();
  Strengthener s(c,m);
  s.strengthen_literal(f);
  return 0;
}