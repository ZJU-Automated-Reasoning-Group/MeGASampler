//
// Created by batchen on 28/04/2022.
//

#include "z3_utils.h"

z3::expr negate_condition(const z3::expr& cond){
  if (cond.num_args() < 2){
    throw UnsupportedOperator();
  } else {
    const z3::expr& arg0 = cond.arg(0);
    const z3::expr& arg1 = cond.arg(1);
    Z3_decl_kind op = get_op(cond);
    if (is_op_le(op)) return arg0 > arg1;
    if (is_op_lt(op)) return arg0 >= arg1;
    if (is_op_ge(op)) return arg0 < arg1;
    if (is_op_gt(op)) return arg0 <= arg1;
    if (is_op_eq(op)) return arg0 != arg1;
    if (is_op_distinct(op)) return arg0 == arg1;
    throw UnsupportedOperator();
  }
}

bool model_eval_to_bool(const z3::model& model, const z3::expr& bool_expr){
  assert(bool_expr.is_bool());
  return model.eval(bool_expr, true).is_true();
}

bool is_lt(const z3::expr& expr){
  auto op = get_op(expr);
  return is_op_lt(op);
}

bool is_gt(const z3::expr& expr){
  auto op = get_op(expr);
  return is_op_gt(op);
}

bool is_eq(const z3::expr& expr){
  auto op = get_op(expr);
  return is_op_eq(op);
}

bool is_distinct(const z3::expr& expr){
  auto op = get_op(expr);
  return is_op_distinct(op);
}

bool is_le(const z3::expr& expr){
  auto op = get_op(expr);
  return is_op_le(op);
}

bool is_ge(const z3::expr& expr){
  auto op = get_op(expr);
  return is_op_ge(op);
}

Z3_decl_kind get_op(const z3::expr& expr){
  assert(expr.is_app());
  return expr.decl().decl_kind();
}

bool is_binary_boolean(const z3::expr& expr){
  Z3_decl_kind op = get_op(expr);
  return (is_op_lt(op) || is_op_le(op) || is_op_gt(op) || is_op_ge(op) || is_op_eq(op) || is_op_distinct(op));
}

z3::expr simplify_strict_to_nonstrict(const z3::expr& expr){
  assert(expr.num_args() == 2);
  const z3::expr& arg0 = expr.arg(0);
  const z3::expr& arg1 = expr.arg(1);
  Z3_decl_kind op = get_op(expr);
  if (is_op_gt(op)){
    return arg0 >= arg1 + 1;
  } else if (is_op_lt(op)){
    return arg0 <= arg1 - 1;
  } else {
    throw UnsupportedOperator();
  }
}