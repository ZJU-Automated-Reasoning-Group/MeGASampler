//
// Created by batchen on 28/04/2022.
//

#ifndef MEGASAMPLER_Z3_UTILS_H
#define MEGASAMPLER_Z3_UTILS_H

#include <z3++.h>

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
