#include "strengthener.h"
#include <iostream>
#include "z3_utils.h"

void Strengthener::strengthen_literal(const z3::expr& literal){
    if (literal.is_bool() && literal.is_const()){
      // case e=true/false/b/!b (where b is a boolean var)
      return; // TODO: this is what we do in Python. Is it correct?
    } else if (literal.is_not()){
      const z3::expr& argument = literal.arg(0);
      if (argument.is_const()){
        // case Not(true/false/b/!b) (where b is a boolean var)
        strengthen_literal(argument);
      } else {
        strengthen_literal(negate_condition(argument));
      }
    }
}

int main() {
  std::cout << "strengthener!!\n";
  return 0;
}