#ifndef STRENGTHENER_H
#define STRENGTHENER_H

#include "intervalmap.h"
#include "z3++.h"

class Strengthener{

    z3::context& c;
    z3::model& model;
    IntervalMap i_map;

public:
    Strengthener(z3::context& con, z3::model& mod) : c(con), model(mod) {};
    class NoRuleForStrengthening : std::exception {};
    void strengthen_literal(const z3::expr& literal); // _strengthen_conjunct in python
private:
    void strengthen_binary_bool_literal(const z3::expr& lhs, int64_t lhs_value, int64_t rhs_value, Z3_decl_kind op);
};

#endif // STRENGTHENER_H
