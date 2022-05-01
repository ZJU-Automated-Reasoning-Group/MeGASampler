//
// Created by batchen on 28/04/2022.
//

#ifndef MEGASAMPLER_Z3_UTILS_H
#define MEGASAMPLER_Z3_UTILS_H

#include <z3++.h>

bool is_op_le(Z3_decl_kind op);
bool is_op_lt(Z3_decl_kind op);
bool is_op_ge(Z3_decl_kind op);
bool is_op_gt(Z3_decl_kind op);
bool is_op_eq(Z3_decl_kind op);
bool is_op_distinct(Z3_decl_kind op);
bool is_op_add(Z3_decl_kind op);
bool is_op_sub(Z3_decl_kind op);
bool is_op_mul(Z3_decl_kind op);
bool is_op_div(Z3_decl_kind op);
bool is_op_rem(Z3_decl_kind op);
bool is_op_mod(Z3_decl_kind op);
bool is_op_and(Z3_decl_kind op);
bool is_op_or(Z3_decl_kind op);
bool is_op_not(Z3_decl_kind op);
bool is_op_uminus(Z3_decl_kind op);
bool is_op_select(Z3_decl_kind op);
bool is_op_store(Z3_decl_kind op);
bool is_op_ite(Z3_decl_kind op);
bool is_op_uninterpreted(Z3_decl_kind op);

class UnsupportedOperator : std::exception {};
z3::expr negate_condition(const z3::expr& condition);
bool is_binary_boolean(const z3::expr& expr);
bool model_eval_to_bool(const z3::model& model, const z3::expr& bool_expr);
int64_t model_eval_to_int64(const z3::model& model, const z3::expr& int64_expr);
bool is_lt(const z3::expr& expr);
bool is_le(const z3::expr& expr);
bool is_gt(const z3::expr& expr);
bool is_ge(const z3::expr& expr);
bool is_eq(const z3::expr& expr);
bool is_distinct(const z3::expr& expr);
Z3_decl_kind get_op(const z3::expr& expr);
z3::expr simplify_strict_to_nonstrict(const z3::expr& expr);
std::string op_to_string(Z3_decl_kind op);
bool is_numeral_constant(const z3::expr& expr);
Z3_decl_kind reverse_bool_op(Z3_decl_kind op);

#endif //MEGASAMPLER_Z3_UTILS_H
