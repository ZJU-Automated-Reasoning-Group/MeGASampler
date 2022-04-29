#include "strengthener.h"
#include <iostream>
#include "z3_utils.h"

void Strengthener::strengthen_literal(const z3::expr& literal){
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
//      std::cout<< "negating: " << argument.to_string() << "\n";
//      std::cout<< "result: " << negate_condition(argument).to_string() << "\n";
      strengthen_literal(negate_condition(argument));
    }
  } else if (is_binary_boolean(literal)){
    const z3::expr& lhs = literal.arg(0);
    if (!lhs.is_int()) throw NoRuleForStrengthening();
    const z3::expr rhs = literal.arg(1);
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
  //TODO: implement
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
  z3::expr f = (!(x != 5)); // should work
//  z3::expr f = (x+y)*z > 5; // should work
  z3::solver solver(c);
  solver.add(f);
  auto res = solver.check();
  assert(res == z3::sat);
  z3::model m = solver.get_model();
  Strengthener s(c,m);
  std::cout << "calling strengthen_literal!!\n";
  s.strengthen_literal(f);
  return 0;
}