//
// Created by batchen on 28/04/2022.
//

#ifndef MEGASAMPLER_Z3_UTILS_H
#define MEGASAMPLER_Z3_UTILS_H

#include <z3++.h>

bool is_op_le(Z3_decl_kind op) {return op==Z3_OP_LE || op==Z3_OP_SLEQ;}
bool is_op_lt(Z3_decl_kind op) {return op==Z3_OP_LT || op==Z3_OP_SLT;}
bool is_op_ge(Z3_decl_kind op) {return op==Z3_OP_GE || op==Z3_OP_SGEQ;}
bool is_op_gt(Z3_decl_kind op) {return op==Z3_OP_GT || op==Z3_OP_SGT;}
bool is_op_eq(Z3_decl_kind op) {return op==Z3_OP_EQ;}
bool is_op_distinct(Z3_decl_kind op) {return op==Z3_OP_DISTINCT;}
bool is_op_add(Z3_decl_kind op) {return op==Z3_OP_ADD || op==Z3_OP_BADD;}
bool is_op_sub(Z3_decl_kind op) {return op==Z3_OP_SUB || op==Z3_OP_BSUB;}
bool is_op_mul(Z3_decl_kind op) {return op==Z3_OP_MUL || op==Z3_OP_BMUL;}
bool is_op_div(Z3_decl_kind op) {return op==Z3_OP_DIV || op==Z3_OP_IDIV || op==Z3_OP_BSDIV || op==Z3_OP_BSDIV0 || op==Z3_OP_BUDIV || op==Z3_OP_BUDIV0;}
bool is_op_rem(Z3_decl_kind op) {return op==Z3_OP_REM || op==Z3_OP_BSREM || op==Z3_OP_BSREM0 || op==Z3_OP_BUREM || op==Z3_OP_BUREM0;}
bool is_op_mod(Z3_decl_kind op) {return op==Z3_OP_MOD || op==Z3_OP_BSMOD || op==Z3_OP_BSMOD0;}
bool is_op_and(Z3_decl_kind op) {return op==Z3_OP_AND || op==Z3_OP_BAND || op==Z3_OP_BREDAND;}
bool is_op_or(Z3_decl_kind op) {return op==Z3_OP_OR || op==Z3_OP_BOR || op==Z3_OP_BREDOR;}
bool is_op_not(Z3_decl_kind op) {return op==Z3_OP_NOT;}
bool is_op_uminus(Z3_decl_kind op) {return op==Z3_OP_UMINUS;}
bool is_op_select(Z3_decl_kind op) {return op==Z3_OP_SELECT;}
bool is_op_store(Z3_decl_kind op) {return op==Z3_OP_STORE;}
bool is_op_ite(Z3_decl_kind op) {return op==Z3_OP_ITE;}
bool is_op_uninterpreted(Z3_decl_kind op) {return op==Z3_OP_UNINTERPRETED;}

class UnsupportedOperator : std::exception {};
z3::expr negate_condition(const z3::expr& condition);
bool is_binary_boolean(const z3::expr& expr);
bool model_eval_to_bool(const z3::model& model, const z3::expr& bool_expr);
bool is_lt(const z3::expr& expr);
bool is_le(const z3::expr& expr);
bool is_gt(const z3::expr& expr);
bool is_ge(const z3::expr& expr);
bool is_eq(const z3::expr& expr);
bool is_distinct(const z3::expr& expr);
Z3_decl_kind get_op(const z3::expr& expr);
z3::expr simplify_strict_to_nonstrict(const z3::expr& expr);

#endif //MEGASAMPLER_Z3_UTILS_H
