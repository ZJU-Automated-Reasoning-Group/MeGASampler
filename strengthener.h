#ifndef STRENGTHENER_H
#define STRENGTHENER_H

#include <list>
#include <unordered_set>

#include "interval.h"
#include "intervalmap.h"
#include "z3++.h"

class Strengthener {
  z3::context& c;
  z3::model& model;
  bool debug;
  // maps an array name to a map from index value to all the index expressions
  // in the array that get this value in the model
  std::unordered_map<std::string,
                     std::unordered_map<int64_t, std::unordered_set<z3::expr>>>
      array_equivalence_classes;

 public:
  IntervalMap i_map;

  Strengthener(z3::context& con, z3::model& mod, bool deb)
      : c(con), model(mod), debug(deb){};
  class NoRuleForStrengthening : std::exception {};
  void strengthen_literal(
      const z3::expr& literal);  // _strengthen_conjunct in python
  void print_interval_map();

 private:
  void strengthen_binary_bool_literal(const z3::expr& lhs, int64_t lhs_value,
                                      int64_t rhs_value, Z3_decl_kind op);
  void strengthen_add(const z3::expr& lhs, int64_t lhs_value,
                      std::list<int64_t>& arguments_values, Z3_decl_kind op,
                      int64_t rhs_value);
  void strengthen_add_without_constants(const z3::expr& lhs, int64_t lhs_value,
                                        std::list<int64_t>& arguments_values,
                                        Z3_decl_kind op, int64_t rhs_value);
  void strengthen_mult(const z3::expr& lhs, int64_t lhs_value,
                       std::list<int64_t>& arguments_values, Z3_decl_kind op,
                       int64_t rhs_value);
  void strengthen_mult_by_constant(const z3::expr& non_constant_arg,
                                   int64_t non_constant_arg_value,
                                   int64_t constant_value, int64_t rhs_value,
                                   Z3_decl_kind op);
  void strengthen_mult_without_constants(const z3::expr& lhs, int64_t lhs_value,
                                         std::list<int64_t>& arguments_values,
                                         Z3_decl_kind op, int64_t rhs_value);
  void strengthen_sub(const z3::expr& lhs, std::list<int64_t>& arguments_values,
                      Z3_decl_kind op, int64_t rhs_value);
  void add_interval(const z3::expr& lhs, int64_t rhs_value, Z3_decl_kind op);
  void add_interval_wrapper(const z3::expr& lhs, int64_t rhs_value,
                            Z3_decl_kind op);
};

#endif  // STRENGTHENER_H
