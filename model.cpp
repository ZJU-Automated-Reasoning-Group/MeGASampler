//
// Created by batchen on 03/02/2022.
//

#include "model.h"

#include <cstdint>
#include <random>

static inline int64_t safe_add(int64_t a, int64_t b) {
  int64_t ret;
  if (!__builtin_add_overflow(a, b, &ret)) return ret;
  return ((a > 0) & (b > 0))
             ? INT64_MAX
             : INT64_MIN;  // TODO: fix for opposite signs? If there is overflow
                           // the value will be wrong anyway
}

static inline int64_t safe_mul(int64_t a, int64_t b) {
  int64_t ret;
  if (!__builtin_mul_overflow(a, b, &ret)) return ret;
  return ((a > 0) ^ (b > 0)) ? INT64_MIN : INT64_MAX;
}

static inline int64_t draw_random_int() {
  std::mt19937 rng(std::random_device{}());
  std::uniform_int_distribution<int64_t> gen(INT64_MIN,
                                             INT64_MAX);  // uniform, unbiased
  return gen(rng);
}

bool Model::addIntAssignment(const std::string& var, int64_t value) {
  auto ret = variable_map.insert(std::pair(var, value));
  return ret.second;
}

bool Model::addArrayAssignment(const std::string& array, int64_t index,
                               int64_t value) {
  std::map<int64_t, int64_t> idx_val_map;
  idx_val_map.insert(std::pair<int64_t, int64_t>(index, value));
  const auto ret = array_map.insert(std::pair(array, idx_val_map));
  if (ret.second) {  // array not in map
    return ret.second;
  } else {  // array in map, but maybe index isn't
    const auto ret2 = ret.first->second.insert(std::pair(index, value));
    return ret2.second;
  }
}

std::string Model::toString() {
  std::string res;
  // lets estimate the string size to prevent reallocation
  res.reserve(10 + variable_map.size() * 10 + array_map.size() * 25);
  for (const auto& name : var_names) {
    const auto var_value = variable_map.find(name);
    if (var_value != variable_map.end()) {
      res += var_value->first;
      res += ':';
      res += std::to_string(var_value->second);
      res += ';';
      continue;
    }
    const auto array_value = array_map.find(name);
    if (array_value != array_map.end()) {
      res += array_value->first;
      res += ":[";
      auto& idx_val_map = array_value->second;
      res += std::to_string(idx_val_map.size());  // #entries
      res += ',';
      res += '0';  // default value. TODO: choose randomly? this value has no
                   // impact on the formula anyway
      res += ',';
      for (const auto it : idx_val_map) {
        res += std::to_string(it.first);  // index
        res += "->";
        res += std::to_string(it.second);  // value
        res += ',';
      }
      res += "];";
      continue;
    }
    assert(false);
  }
  return res;
}

std::pair<int64_t, bool> Model::evalIntVar(const std::string& var) {
  auto it = variable_map.find(var);
  if (it == variable_map.end()) {
    return std::pair<int64_t, bool>(-1, false);
  } else {
    return std::pair<int64_t, bool>(it->second, true);
  }
}

std::pair<int64_t, bool> Model::evalArrayVar(const std::string& array,
                                             int64_t index) {
  auto it = array_map.find(array);
  if (it == array_map.end()) {
    return std::pair<int64_t, bool>(-1, false);
  } else {
    auto& curr_array_map = it->second;
    auto it2 = curr_array_map.find(index);
    if (it2 == curr_array_map.end()) {
      return std::pair<int64_t, bool>(-1, false);
    } else {
      return std::pair<int64_t, bool>(it2->second, true);
    }
  }
}

std::pair<int64_t, bool> Model::evalIntExpr(const z3::expr& e, bool debug,
                                            bool model_completion) {
  if (debug) std::cout << "eval int expr on: " << e.to_string() << "\n";
  assert(z3::is_int(e));
  assert(e.is_app());
  z3::func_decl fd = e.decl();
  if (e.is_const()) {
    int i;
    if (e.is_numeral_i(i)) {
      if (debug) std::cout << "found numeral: " << std::to_string(i) << "\n";
      return std::pair<int64_t, bool>(i, true);
    }
    std::string name = fd.name().str();
    if (debug) std::cout << "found const: " << name << "\n";
    auto res = evalIntVar(name);
    if (model_completion && !res.second) {
      int64_t rand = draw_random_int();
      auto r = addIntAssignment(name, rand);
      assert(r);
      if (debug)
        std::cout << "returning mc rand value: " << std::to_string(rand)
                  << "\n";
      return std::pair<int64_t, bool>(rand, true);
    } else {
      if (debug)
        std::cout << "returning existing value for int var: "
                  << std::to_string(res.first) << "\n";
      return res;
    }
  } else if (fd.decl_kind() == Z3_OP_SELECT) {
    auto array = e.arg(0);
    auto index = e.arg(1);
    std::pair<int64_t, bool> index_res =
        evalIntExpr(index, debug, model_completion);
    if (index_res.second) {
      std::string array_name = array.decl().name().str();
      auto res = evalArrayVar(array_name, index_res.first);
      if (model_completion && !res.second) {
        int64_t rand = draw_random_int();
        auto r = addArrayAssignment(array_name, index_res.first, rand);
        assert(r);
        if (debug)
          std::cout << "returning mc rand value for array: "
                    << std::to_string(rand) << "\n";
        return std::pair<int64_t, bool>(rand, true);
      } else {
        if (debug)
          std::cout << "returning existing value for array: "
                    << std::to_string(res.first) << "\n";
        return res;
      }
    } else {
      return index_res;
    }
  }
  std::vector<int64_t> children_values;
  for (unsigned int i = 0; i < e.num_args(); i++) {
    auto arg = e.arg(i);
    std::pair<int64_t, bool> res_arg =
        evalIntExpr(arg, debug, model_completion);
    if (!res_arg.second) {
      return res_arg;
    } else {
      children_values.push_back(res_arg.first);
    }
  }
  switch (fd.decl_kind()) {
    case Z3_OP_ADD: {
      if (debug) std::cout << "found add\n";
      int64_t sum = 0;
      for (std::vector<int64_t>::iterator it = children_values.begin();
           it != children_values.end(); ++it) {
        sum = safe_add(sum, *it);
      }
      if (debug)
        std::cout << "returning sum result: " << std::to_string(sum) << "\n";
      return std::pair<int64_t, bool>(sum, true);
    }
    case Z3_OP_MUL: {
      if (debug) std::cout << "found mul\n";
      int64_t prod = 1;
      for (std::vector<int64_t>::iterator it = children_values.begin();
           it != children_values.end(); ++it) {
        prod = safe_mul(prod, *it);
      }
      if (debug)
        std::cout << "returning mult result: " << std::to_string(prod) << "\n";
      return std::pair<int64_t, bool>(prod, true);
    }
    case Z3_OP_SUB: {
      if (debug) std::cout << "found sub\n";
      assert(children_values.size() == 2);
      int64_t sub = safe_add(
          children_values[0],
          -children_values[1]);  // TODO: can unary minus computation overflow?
      if (debug)
        std::cout << "returning sub result: " << std::to_string(sub) << "\n";
      return std::pair<int64_t, bool>(sub, true);
    }
    case Z3_OP_UMINUS: {
      if (debug) std::cout << "found uminus\n";
      assert(children_values.size() == 1);
      if (debug)
        std::cout << "returning uminus result: "
                  << std::to_string(-children_values[0]) << "\n";
      return std::pair<int64_t, bool>(
          -children_values[0],
          true);  // TODO: can unary minus computation overflow?
    }
    default: {
      if (debug) std::cout << "unknown op: " << fd.decl_kind() << "\n";
      return std::pair<int64_t, bool>(-1, false);
    }
  }
}
