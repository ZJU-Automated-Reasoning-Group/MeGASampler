
#include "strengthener.h"

int main() {
  std::cout << "Hello strengthener!!\n";
  z3::context c;
  z3::expr x = c.int_const("x");
  z3::expr y = c.int_const("y");
  z3::expr z = c.int_const("z");
  z3::expr b1 = c.bool_const("b1");
  z3::expr b2 = c.bool_const("b2");
//  z3::expr f = b1 == b2; // NoRuleForStrengthening
//  z3::expr f = x*y*z > 5; // should work
//  z3::expr f = (!(x != 5)); // should work
//  z3::expr f = (x*y)-z < 9; // should work
//  z3::expr f = !((x*y)-z < 9); // should work
//  z3::expr f = !((x*0)-z <= 9); // should work
//  z3::expr f = b1; // should work
//  z3::expr f = !b2; // should work
//  z3::expr f = 3*(x+4) != 20; // should work
//  z3::expr f = 3*(x+4) != x; // assertion failure - rhs is not a number
//  z3::expr f = (x+y)*z > 5; // should work
//  z3::expr f = (x+y)+4+z+(-2) > 5; // should work
//  z3::expr f = (-x)-y+2*z > 50; // should work
//  z3::expr f = 3*x*5*y > 50; // should work
  z3::expr f = 3-(4*x+y*z) < 80; // should work
  z3::solver solver(c);
  solver.add(f);
  auto res = solver.check();
  assert(res == z3::sat);
  z3::model m = solver.get_model();
  Strengthener s(c,m);
  s.print_interval_map();
  s.strengthen_literal(f);
  s.print_interval_map();
//  Interval i1;
//  std::cout << "infinite interval: " << i1 << "\n";
//  i1.set_lower_bound(45);
//  i1.set_upper_bound(45);
//  std::cout << "singelton interval: " << i1 << "\n";
//  i1.set_lower_bound(90);
//  std::cout << "empty interval: " << i1 << "\n";
//  i1.set_lower_bound(90);
//  std::cout << "empty interval: " << i1 << "\n";
//  i1.set_upper_bound(900);
//  std::cout << "empty interval: " << i1 << "\n";
//  i1.set_lower_bound(-90);
//  std::cout << "empty interval: " << i1 << "\n";
//  Interval i2;
//  std::cout << "infinite interval: " << i2 << "\n";
//  i2.set_lower_bound(-400);
//  std::cout << "from -400: " << i2 << "\n";
//  i2.set_upper_bound(0);
//  std::cout << "to 0: " << i2 << "\n";
//  i2.set_upper_bound(60);
//  std::cout << "no change" << i2 << "\n";
//  i2.set_upper_bound(-60);
//  std::cout << "to -60: " << i2 << "\n";
//  i2.set_lower_bound(-4000);
//  std::cout << "no change: " << i2 << "\n";
//  i2.set_lower_bound(-120);
//  std::cout << "from -120: " << i2 << "\n";
//  i2.set_upper_bound(-500);
//  std::cout << "empty: " << i2 << "\n";
  return 0;
}
