//
// Created by batchen on 28/04/2022.
//

#include "z3_utils.h"

z3::expr negate_condition(const z3::expr& condition){
  // TODO: implement
  return condition;
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
  //TODO: implement
  return false;
}

z3::expr simplify_strict_to_nonstrict(const z3::expr& expr){
  //TODO: implement
  return z3::expr(expr.ctx());
}