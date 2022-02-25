#ifndef MEGASAMPLER_MODEL_H
#define MEGASAMPLER_MODEL_H

#include <z3++.h>

#include <iostream>
#include <map>
#include <string>
#include <vector>

class Model {
  const std::vector<std::string>& var_names;  // Memory shenanigans :)
  std::map<std::string, int64_t> variable_map;
  std::map<std::string, std::map<int64_t, int64_t>> array_map;

 public:
  Model(const std::vector<std::string>& _var_names)
      : var_names(_var_names), variable_map(), array_map() {}

  /* Returns true iff assignment was successful (i.e, var was not previously
   * assigned).
   */
  bool addIntAssignment(const std::string& var, int64_t value);
  // Returns true iff assignment was successful (i.e, array[index] was not
  // previously assigned).
  bool addArrayAssignment(const std::string& array, int64_t index,
                          int64_t value);
  std::string toString();
  /*
   * If var is assigned in the current model - returns its value in the model
   * and true. Else - returns -1 and false.
   */
  std::pair<int64_t, bool> evalIntVar(const std::string& var);
  /*
   * If array[index] is assigned in the current model - returns its value in the
   * model and true. Else - returns -1 and false.
   */
  std::pair<int64_t, bool> evalArrayVar(const std::string& array,
                                        int64_t index);
  /*
   * If all variables in e are assigned in the current model - returns the value
   * of e in the model and true. Else - returns -1 and false. If
   * model_completion flag is on, the result will always be true and variables
   * (or array accesses with constant indices) in e that are not assigned will
   * be assigned a random value (in this case the model itself changes).
   */
  std::pair<int64_t, bool> evalIntExpr(const z3::expr& e, bool debug = false,
                                       bool model_completion = false);
};

#endif  // MEGASAMPLER_MODEL_H
