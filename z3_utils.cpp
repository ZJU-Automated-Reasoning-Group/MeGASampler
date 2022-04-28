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
    if (is_le(cond)) return arg0 > arg1;
    if (is_lt(cond)) return arg0 >= arg1;
    if (is_ge(cond)) return arg0 < arg1;
    if (is_gt(cond)) return arg0 <= arg1;
    if (is_eq(cond)) return arg0 != arg1;
    if (is_distinct(cond)) return arg0 == arg1;
    throw UnsupportedOperator();
  }
}

bool model_eval_to_bool(const z3::model& model, const z3::expr& bool_expr){
  assert(bool_expr.is_bool());
  return model.eval(bool_expr, true).is_true();
}

bool is_lt(const z3::expr& expr){
  auto op = get_op(expr);
  return op==Z3_OP_LT || op==Z3_OP_SLT || op==Z3_OP_ULT;
}

bool is_gt(const z3::expr& expr){
  auto op = get_op(expr);
  return op==Z3_OP_GT || op==Z3_OP_SGT || op==Z3_OP_UGT;
}

bool is_eq(const z3::expr& expr){
  auto op = get_op(expr);
  return op==Z3_OP_EQ;
}

bool is_distinct(const z3::expr& expr){
  auto op = get_op(expr);
  return op==Z3_OP_DISTINCT;
}

bool is_le(const z3::expr& expr){
  auto op = get_op(expr);
  return op==Z3_OP_LE || op==Z3_OP_SLEQ || op==Z3_OP_ULEQ;
}

bool is_ge(const z3::expr& expr){
  auto op = get_op(expr);
  return op==Z3_OP_GE || op==Z3_OP_SGEQ || op==Z3_OP_UGEQ;
}

Z3_decl_kind get_op(const z3::expr& expr){
  assert(expr.is_app());
  return expr.decl().decl_kind();
}

bool is_binary_boolean(const z3::expr& expr){
  return (is_lt(expr) || is_le(expr) || is_gt(expr) || is_ge(expr) || is_eq(expr) || is_distinct(expr));
}

z3::expr simplify_strict_to_nonstrict(const z3::expr& expr){
  assert(expr.num_args() == 2);
  const z3::expr& arg0 = expr.arg(0);
  const z3::expr& arg1 = expr.arg(1);
  if (is_gt(expr)){
    return arg0 >= arg1 + 1;
  } else if (is_lt(expr)){
    return arg0 <= arg1 - 1;
  } else {
    throw UnsupportedOperator();
  }
}