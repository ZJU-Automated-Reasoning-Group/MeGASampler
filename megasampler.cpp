#include "megasampler.h"

#include <capnp/serialize.h>

#include <cinttypes>
#include <cstdint>
#include <iostream>
#include <random>
#include <set>

#include "model.h"
#include "pythonfuncs.h"
#include "strengthener.h"
#include "strengthen.capnp.h"

void MEGASampler::print_array_equality_graph(){
  std::cout << "array equality graph:\n";
  for (auto it=arrayEqualityGraph.begin(); it!=arrayEqualityGraph.end(); ++it){
    std::cout << it->first << " =>\n";
    for (auto it2=it->second.begin(); it2!=it->second.end(); ++it2){
      std::cout << it2->toString() << "\n";
    }
  }
}

static inline bool is_array_eq(const z3::expr& e){
  return e.is_eq() && e.arg(0).is_array();
}

static inline bool check_if_in_interval(
    int64_t val, const MEGASampler::capnpInterval& interval) {
  return (val >= interval.getLow() && val <= interval.getHigh());
}

static int count_selects(const z3::expr& e) {
  if (!e.is_app()) return 0;
  int count = (e.decl().decl_kind() == Z3_OP_SELECT);
  for (unsigned int i = 0; i < e.num_args(); i++) {
    count += count_selects(e.arg(i));
  }
  return count;
}

static inline void save_store_index_and_value(const z3::expr& e, z3::expr_vector& indices, z3::expr_vector& values, z3::expr& a){
  assert(e.is_array());
  if (e.is_const()){
    a = e;
  } else if (e.is_app() && e.decl().decl_kind() == Z3_OP_STORE){
    indices.push_back(e.arg(1));
    values.push_back(e.arg(2));
    save_store_index_and_value(e.arg(0), indices, values, a);
  } else {
    std::cout << e.to_string() << "\n";
    assert(false);
  }
}

static inline void extract_array_from_store(const z3::expr& e, z3::expr& array){
    assert(e.is_array());
    if (e.is_const()){
        array = e;
    } else if (e.is_app() && e.decl().decl_kind() == Z3_OP_STORE){
        extract_array_from_store(e.arg(0), array);
    } else {
      std::cout << e.to_string() << "\n";
      assert(false);
    }
}

void MEGASampler::register_array_eq(z3::expr& f){
  if (is_array_eq(f)) {
    const z3::expr& left_a = f.arg(0);
    const z3::expr& right_a = f.arg(1);
    arrayEqualityEdge st_eq(c);
    st_eq.store_e = f;
    save_store_index_and_value(left_a, st_eq.a_indices, st_eq.a_values, st_eq.a);
    save_store_index_and_value(right_a, st_eq.b_indices, st_eq.b_values, st_eq.b);
    arrayEqualityGraph[st_eq.a.to_string()].push_back(st_eq);
    if (!z3::eq(st_eq.a, st_eq.b)) {
      arrayEqualityGraph[st_eq.b.to_string()].push_back(st_eq);
    }
  } else {
    for (auto child : f){
      register_array_eq(child);
    }
  }
}

/*
 * search for a sub-expr e of the form store(..(store(a,..))=store(..(store(b,..)) in f.
 * return a,b and e
 */
static inline bool find_eq_of_different_arrays(z3::expr& f, z3::expr& a, z3::expr& b, z3::expr& e){
    if (is_array_eq(f)) {
//        std::cout << "array eq found: " << f.to_string() << "\n";
        z3::expr left_a = f.arg(0);
        z3::expr right_a = f.arg(1);
        extract_array_from_store(left_a, a);
        extract_array_from_store(right_a, b);
        e = f;
        return (a.to_string() != b.to_string());
    } else {
        for (auto child : f){
            bool res = find_eq_of_different_arrays(child, a, b, e);
            if (res) return res;
        }
        return false;
    }
}

static inline z3::expr store_substitute(z3::expr& store_e, z3::expr& array_e, z3::expr& aux_array_e){
    if (store_e.is_app() && store_e.decl().decl_kind() == Z3_OP_STORE){
        z3::expr smaller_array_e = store_e.arg(0);
        z3::expr index_e = store_e.arg(1);
        z3::expr value_e = store_e.arg(2);
        z3::expr smaller_array_prime = store_substitute(smaller_array_e, array_e, aux_array_e);
        z3::expr_vector src_e(store_e.ctx());
        z3::expr_vector dst_e(store_e.ctx());
        src_e.push_back(smaller_array_e);
        dst_e.push_back(smaller_array_prime);
        src_e.push_back(value_e);
        dst_e.push_back(z3::select(array_e, index_e));
        return store_e.substitute(src_e,dst_e);
    } else {
        assert(store_e == array_e);
        return aux_array_e;
    }
}

MEGASampler::MEGASampler(std::string _input, std::string _output_dir,
                         int _max_samples, double _max_time,
                         int _max_epoch_samples, double _max_epoch_time,
                         int _strategy, bool _json, bool _blocking)
    : Sampler(_input, _output_dir, _max_samples, _max_time, _max_epoch_samples,
              _max_epoch_time, _strategy, _json, _blocking),
      simpl_formula(c), implicant(c) {
  simplify_formula();
  initialize_solvers();
  std::cout << "starting MeGASampler" << std::endl;
}

static inline void collect_z3_names(z3::expr& formula, std::set<std::string>& z3names_set, z3::expr_vector& z3var_vector){
    if (formula.is_const()){
        std::string const_name = formula.decl().name().str();
        if (const_name.rfind("z3name!",0) == 0 ){
            auto res = z3names_set.insert(const_name);
            if (res.second){
                z3var_vector.push_back(formula);
            }
        }
    } else {
        for (z3::expr child : formula){
            collect_z3_names(child, z3names_set, z3var_vector);
        }
    }
}

z3::expr MEGASampler::rename_z3_names(z3::expr& formula){
    std::set<std::string> z3_names_set;
    z3::expr_vector z3_var_vector(c);
    collect_z3_names(formula, z3_names_set, z3_var_vector);
    assert(z3_names_set.size() == z3_var_vector.size());
    if (debug) {
        std::cout << "names found: ";
        for (const auto name_var: z3_names_set) {
            std::cout << name_var << ",";
        }
        std::cout << "\n";
    }
    z3::expr_vector new_vars_vector(c);
    for (auto var : z3_var_vector){
        assert(var.is_const());
        std::string name = var.to_string();
        std::string new_name = "mega!" + name;
        z3::expr new_var = c.constant(new_name.c_str(), var.get_sort());
        new_vars_vector.push_back(new_var);
    }
    return formula.substitute(z3_var_vector, new_vars_vector);
}

//TODO: implement these missing funtions here
//assert(is_lhs(simpl_formula));
//assert(no_select_store(simpl_formula));
//assert(is_nnf(simpl_formula));
//assert(no_z3_name(simpl_formula));

void MEGASampler::simplify_formula(){

//  // first nnf conversion - to get rid of ite in expr for eliminate_array_eq
//  z3::goal g(c);
//  g.add(original_formula);
//  const z3::tactic nnf_t(c, "nnf");
//  const auto nnf_ar = nnf_t(g);
//  assert(nnf_ar.size() == 1);
//  auto nnf_formula = nnf_ar[0].as_expr();
//  if (debug) std::cout << "after first nnf conversion: " << nnf_formula.to_string() << "\n";
//  original_formula = nnf_formula; // for next stage. TODO: change this once next stage doesn't need it
//
//  // lose array equalities
//  g = z3::goal(c);
//  eliminate_eq_of_different_arrays(); // reads and changes original_formula //TODO: avoid changing original_formula
//  g.add(original_formula);
//  z3::params simplify_params(c);
//  simplify_params.set("expand_store_eq", true);
//  auto simp_ar = z3::with(z3::tactic(c, "simplify"), simplify_params)(g);
//  assert(simp_ar.size() == 1);
//  auto simp_formula = simp_ar[0].as_expr();
//  //  TODO: make sure it removes store(a,..)=a, a=a, and nested stores;
//  if (debug) std::cout << "after losing array eq: " << simp_formula.to_string() << "\n";

  register_array_eq(original_formula);
  print_array_equality_graph();

  // arith_lhs + lose select(store())
  z3::goal g(c);
  g.add(original_formula);
  z3::params simplify_params(c);
//  simplify_params = z3::params(c);
  simplify_params.set("arith_lhs", true);
  simplify_params.set("blast_select_store", true);
  auto simp_ar = z3::with(z3::tactic(c, "simplify"), simplify_params)(g);
//  simp_ar = z3::with(z3::tactic(c, "simplify"), simplify_params)(g);
  assert(simp_ar.size() == 1);
  auto simp_formula = simp_ar[0].as_expr();
  if (debug) std::cout << "after arith_lhs+blast_select_store: " << simp_formula.to_string() << "\n";

  // nnf conversion- to make sure its nnf + get rid of ite in expr
  g = z3::goal(c);
  g.add(simp_formula);
  const z3::tactic nnf_t2(c, "nnf");
  const auto nnf_ar2 = nnf_t2(g);
  assert(nnf_ar2.size() == 1);
  auto nnf_formula2 = nnf_ar2[0].as_expr();
  if (debug) std::cout << "after nnf conversion: " << nnf_formula2.to_string() << "\n";

  // final step - rename z3!name to mega!z3!name
  simpl_formula = rename_z3_names(nnf_formula2);
  if (debug) {
    std::cout << "after z3 renaming: " << simpl_formula.to_string() << "\n";
//    TODO: implement asserts
//    assert(is_lhs(simpl_formula));
//    assert(no_select_store(simpl_formula));
//    assert(is_nnf(simpl_formula));
//    assert(no_z3_name(simpl_formula));
  }
}

void MEGASampler::initialize_solvers() {
    opt.add(simpl_formula);  // adds formula as hard constraint to optimization
    // solver (no weight specified for it)
    solver.add(simpl_formula);  // adds formula as constraint to normal solver
}

static void remove_or(z3::expr& formula, const z3::model& m, std::list<z3::expr>& res){
  if (formula.decl().decl_kind() != Z3_OP_OR && formula.decl().decl_kind() != Z3_OP_AND){
    res.push_back(formula);
  } else if (formula.decl().decl_kind() == Z3_OP_OR){
    std::vector<int> satisfied_disjncts_distances;
    int i = 0;
    for (const auto& child: formula){
      if (m.eval(child, true)){
        satisfied_disjncts_distances.push_back(i);
      }
      i++;
    }
    std::random_shuffle(satisfied_disjncts_distances.begin(), satisfied_disjncts_distances.end());
    i = *satisfied_disjncts_distances.begin();
    int j = 0;
    for (auto child: formula) {
      if (j == i) {
        remove_or(child, m, res);
        break;
      }
      j++;
    }
  } else {
    assert(formula.decl().decl_kind() == Z3_OP_AND);
    for (auto child: formula) {
      remove_or(child, m, res);
    }
  }
}

void MEGASampler::add_opposite_array_constraint(const MEGASampler::storeEqIndexValue& curr_ival,
                const MEGASampler::arrayEqualityEdge& store_eq, std::list<z3::expr>& conjuncts){
  const z3::expr& array = (curr_ival.in_a ? store_eq.b : store_eq.a);
  if (!eq(z3::select(array, curr_ival.index_expr), curr_ival.value_expr)) {
    conjuncts.push_back(z3::select(array, curr_ival.index_expr) - curr_ival.value_expr == 0);
  }
}

void MEGASampler::add_value_clash_constraint(const MEGASampler::storeEqIndexValue& curr_ival,
                                const MEGASampler::storeEqIndexValue& next_ival, std::list<z3::expr>& conjuncts){
  if (!eq(next_ival.value_expr, curr_ival.value_expr)) {
    conjuncts.push_back(next_ival.value_expr - curr_ival.value_expr == 0);
  }
}

void MEGASampler::build_index_value_vector(arrayEqualityEdge& store_eq){
  std::vector<storeEqIndexValue>& index_values = store_eq.index_values;
  assert(store_eq.a_indices.size() == store_eq.a_values.size());
  for (unsigned int i = 0; i < store_eq.a_indices.size(); i++) {
    storeEqIndexValue ival(c);
    const z3::expr &model_eval_res = model.eval(store_eq.a_indices[i], true);
    int64_t value;
    assert(model_eval_res.is_numeral_i64(value));
    ival.value = value;
    ival.serial_number_in_array = i;
    ival.index_expr = store_eq.a_indices[i];
    ival.value_expr = store_eq.a_values[i];
    ival.in_a = true;
    index_values.push_back(ival);
  }
  assert(store_eq.b_indices.size() == store_eq.b_values.size());
  for (unsigned int i = 0; i < store_eq.b_indices.size(); i++) {
    storeEqIndexValue ival(c);
    const z3::expr &model_eval_res = model.eval(store_eq.b_indices[i], true);
    int64_t value;
    assert(model_eval_res.is_numeral_i64(value));
    ival.value = value;
    ival.serial_number_in_array = i;
    ival.index_expr = store_eq.b_indices[i];
    ival.value_expr = store_eq.b_values[i];
    ival.in_a = false;
    index_values.push_back(ival);
  }
  // sort the list according to values
  std::sort(index_values.begin(), index_values.end());
}

void MEGASampler::add_index_relationship_constraints(const arrayEqualityEdge& store_eq, std::list<z3::expr>& conjuncts){
  // add index relationship conatraints
  const auto& index_values = store_eq.index_values;
  for (unsigned int i = 0; i < index_values.size()-1 ; i++){
    const auto& curr_ival = index_values[i];
    const auto& next_ival = index_values[i+1];
    if (curr_ival.value < next_ival.value){
      conjuncts.push_back(curr_ival.index_expr - next_ival.index_expr < 0);
    } else {
      assert (curr_ival.value == next_ival.value);
      if (!eq(curr_ival.index_expr,next_ival.index_expr)) {
        std::cout << curr_ival.index_expr.to_string() << "different than " << next_ival.index_expr.to_string() << "\n";
        conjuncts.push_back(curr_ival.index_expr - next_ival.index_expr == 0);
      }
    }
  }
}

void MEGASampler::remove_duplicates_in_index_values(arrayEqualityEdge& store_eq){
  auto& index_values = store_eq.index_values;
  //remove duplicates
  auto it = index_values.begin();
  while (it != index_values.end()){
    auto next_it = it+1;
    auto& curr = *it;
    while (next_it != index_values.end()){
      auto& next = *next_it;
      if (curr.value == next.value && curr.in_a == next.in_a){
        next_it = index_values.erase(next_it);
      } else {
        break;
      }
    }
    it++;
  }
}

void MEGASampler::add_array_value_constraints(const arrayEqualityEdge& store_eq, std::list<z3::expr>& conjuncts){
  const auto& index_values = store_eq.index_values;
  unsigned int curr = 0;
  while (curr < index_values.size()) {
    const auto &curr_ival = index_values[curr];
    bool has_next = curr + 1 < index_values.size();
    if (!has_next){
      add_opposite_array_constraint(curr_ival, store_eq, conjuncts);
      curr++;
    } else {
      const auto &next_ival = index_values[curr + 1];
      if (next_ival.value > curr_ival.value){
        add_opposite_array_constraint(curr_ival, store_eq, conjuncts);
        curr++;
      } else {
        assert(next_ival.value == curr_ival.value && next_ival.in_a != curr_ival.in_a);
        if (curr + 2 < index_values.size()){
          assert(index_values[curr + 2].value != curr_ival.value);
        }
        add_value_clash_constraint(curr_ival, next_ival, conjuncts);
        curr = curr+2;
      }
    }
  }
}

void MEGASampler::remove_array_equalities(std::list<z3::expr>& conjuncts){
  auto it = conjuncts.begin();
  while (it != conjuncts.end()){
    const z3::expr conjunct = *it;
    if (is_array_eq(conjunct)){
      // remove store_eq from imlicant_conjuncts
      it = conjuncts.erase(it);
      // find store_eq in array_equality_graph
      z3::expr a_array(c);
      extract_array_from_store(conjunct.arg(0), a_array);
      for (auto& store_eq : arrayEqualityGraph[a_array.to_string()]){
        if (eq(store_eq.store_e, conjunct)){
          store_eq.in_implicant = true;
          build_index_value_vector(store_eq);
//          std::cout << "index values: \n";
//          for (auto ival2: index_values){
//            std::cout << ival2.to_string() << ",";
//          }
//          std::cout << "\n";
          add_index_relationship_constraints(store_eq, conjuncts);
          remove_duplicates_in_index_values(store_eq);
//          std::cout << "index values after removing duplicates: \n";
//          for (auto ival2: index_values){
//            std::cout << ival2.to_string() << ",";
//          }
//          std::cout << "\n";
          add_array_value_constraints(store_eq, conjuncts);
          // update symmetric edge in the graph
          const z3::expr& b_array = store_eq.b;
          for (auto& store_eq2 : arrayEqualityGraph[b_array.to_string()]){
            if (store_eq2.store_e == conjunct){
              store_eq2.in_implicant = true;
              store_eq2.index_values = store_eq.index_values;
            }
          }
        }
      }
    } else {
      it++;
    }
  }
  std::cout << "conjuncts after removing array eqs (size " << std::to_string(conjuncts.size()) << ": ";
  for (auto conjunct : conjuncts){
    std::cout << conjunct.to_string() << ",";
  }
  std::cout << "\n";
}

void MEGASampler::do_epoch(const z3::model& m) {
  is_time_limit_reached();

  // set all edges of array_eq_graph as non-valid (not in implicant) and empty the index_values vector
  for (auto& entry : arrayEqualityGraph){
    for (auto& array_eq_edge : entry.second){
      array_eq_edge.in_implicant = false;
      array_eq_edge.index_values.clear();
    }
  }

  // compute m-implicant
  std::list<z3::expr> implicant_conjuncts_list;
  remove_or(simpl_formula, m, implicant_conjuncts_list);
  if (debug) {
    std::cout << "after remove or: ";
    for (auto conj: implicant_conjuncts_list){
      assert(conj);
      std::cout << conj.to_string() << ",";
    }
    std::cout << "\n";
  }

  remove_array_equalities(implicant_conjuncts_list);
  std::cout << "after removing array eqs:\n";
  print_array_equality_graph();

  z3::expr_vector implicant_conjuncts(c);
  for (auto conj: implicant_conjuncts_list){
    implicant_conjuncts.push_back(conj);
  }
  implicant = z3::mk_and(implicant_conjuncts);
  struct buflen ret = call_strengthen(implicant, m, has_arrays, debug);
  const auto view = kj::arrayPtr(reinterpret_cast<const capnp::word*>(ret.buf),
                                 ret.len / sizeof(capnp::word));
  // Disable the security measure, we trust ourselves
  const capnp::ReaderOptions options{UINT64_MAX, 64};
  capnp::FlatArrayMessageReader message(view, options);
  auto container = message.getRoot<StrengthenResult>();

  auto res = container.getRes();
  auto failureDescription = container.getFailuredecription();
  if (!res) {
    std::cout << "An error has occurred during epoch: "
              << failureDescription.cStr() << "\n";
    failure_cause = failureDescription.cStr();
    safe_exit(1);
  }

  // print intervals for debug and parse array indices
  std::vector<arrayAccessData> index_vec;
  if (has_arrays && debug) std::cout << "parsing intervals:\n";
  for (auto varinterval : container.getIntervalmap()) {
    std::string varsort = varinterval.getVarsort().cStr();
    std::string varname;
    if (varsort == "int") {
      varname = varinterval.getVariable().cStr();
    } else {
      assert(varsort == "select");
      varname = varinterval.getVariable().cStr();
      std::string index_str = varinterval.getIndex().cStr();
      z3::expr index_expr = deserialise_expr(index_str);
      varname += std::string{"["} + index_expr.to_string() + std::string{"]"};
      int num_selects = count_selects(index_expr);
      arrayAccessData d(varinterval, index_expr, num_selects);
      index_vec.push_back(d);
    }
    auto interval = varinterval.getInterval();
    bool isLowMinf = interval.getIslowminf();
    bool isHighInf = interval.getIshighinf();
    auto low = isLowMinf ? "MINF" : std::to_string(interval.getLow());
    auto high = isHighInf ? "INF" : std::to_string(interval.getHigh());
    if (debug)
      std::cout << varname << ": "
                << "[" << low << "," << high << "] ";
  }
  if (debug) std::cout << "\n";
  std::sort(index_vec.begin(), index_vec.end());
  if (debug) {
    for (auto it = index_vec.begin(); it < index_vec.end(); it++) {
      std::cout << it->toString() << "\n";
    }
  }

  if (use_blocking)
    add_soft_constraint_from_intervals(container.getIntervalmap(), index_vec);

  if (is_time_limit_reached("epoch")) return;

  sample_intervals_in_rounds(container.getIntervalmap(), index_vec);
}

void MEGASampler::finish() {
  json_output["method name"] = "megasampler";
  Sampler::finish();
}

static inline uint64_t ilog2(const uint64_t x) {
  if (0 == x) return 1;  // undefined but useful for me here
  return (63 - __builtin_clzll(x));
}

static inline int64_t safe_mul(const int64_t a, const int64_t b) {
  int64_t ret;
  if (!__builtin_mul_overflow(a, b, &ret)) return ret;
  return ((a > 0) ^ (b > 0)) ? INT64_MIN : INT64_MAX;
}

void MEGASampler::sample_intervals_in_rounds(
    const capnp::List<StrengthenResult::VarInterval>::Reader& intervalmap,
    const std::vector<arrayAccessData>& index_vec) {
  uint64_t coeff = 1;
  for (auto imap : intervalmap) {
    const auto& i = imap.getInterval();
    if (i.getIslowminf() || i.getIshighinf()) {
      coeff += 32;
      continue;
    }
    coeff = safe_mul(coeff, 1 + ilog2(1 + ilog2(1 + i.getHigh() - i.getLow())));
  }
  if (use_blocking) coeff = coeff + intervalmap.size();
  const uint64_t MAX_ROUNDS =
      std::min(std::max(use_blocking ? 50UL : 10UL, coeff),
               (long unsigned)max_samples >> 7UL);
  const unsigned int MAX_SAMPLES = 30;
  const float MIN_RATE = 0.75;
  uint64_t debug_samples = 0;

  if (debug)
    std::cout << "Sampling, coeff = " << coeff
              << ", MAX_ROUNDS = " << MAX_ROUNDS
              << ", MAX_SAMPLES = " << MAX_SAMPLES << "\n";

  float rate = 1.0;
  for (uint64_t round = 0; round < MAX_ROUNDS && rate > MIN_RATE; ++round) {
    is_time_limit_reached();
    unsigned int new_samples = 0;
    unsigned int round_samples = 0;
    for (; round_samples <= MAX_SAMPLES; ++round_samples) {
      std::string sample;
      if (has_arrays) {
        sample = get_random_sample_from_array_intervals(intervalmap, index_vec);
      } else {
        sample = get_random_sample_from_int_intervals(intervalmap);
      }
      ++total_samples;
      if (save_and_output_sample_if_unique(sample)) {
        if (debug) ++debug_samples;
        ++new_samples;
      }
    }
    rate = new_samples / round_samples;
  }
  if (debug)
    std::cout << "Epoch unique samples: " << debug_samples
              << ", rate = " << rate << "\n";
}

int64_t randomInInterval(const MEGASampler::capnpInterval& interval) {
  int64_t low = interval.getLow();
  int64_t high = interval.getHigh();
  std::mt19937 rng(std::random_device{}());
  std::uniform_int_distribution<int64_t> gen(low, high);  // uniform, unbiased
  return gen(rng);
}

std::string MEGASampler::get_random_sample_from_array_intervals(
    const capnpIntervalMap& intervalmap,
    const std::vector<arrayAccessData>& indexvec) {
  while (true) {  // TODO some heuristic for early termination in case we keep
                  // getting clashes?
    Model m_out(variable_names);
    bool valid_model = true;
    for (auto varinterval : intervalmap) {
      std::string varsort = varinterval.getVarsort().cStr();
      if (varsort == "int") {
        std::string varname = varinterval.getVariable().cStr();
        const auto& interval = varinterval.getInterval();
        int64_t rand = randomInInterval(interval);
        bool res = m_out.addIntAssignment(varname, rand);
        assert(res);
      }
    }
    for (auto it : indexvec) {
      int64_t i_val;
      z3::expr index_expr = it.indexExpr;
      auto index_res = m_out.evalIntExpr(index_expr, false, true);
      assert(index_res.second);
      i_val = index_res.first;
      std::string array_name = it.entryInCapnpMap.getVariable().cStr();
      auto res = m_out.evalArrayVar(array_name, i_val);
      if (res.second) {
        valid_model =
            check_if_in_interval(res.first, it.entryInCapnpMap.getInterval());
        if (!valid_model) break;
      } else {
        const auto& interval = it.entryInCapnpMap.getInterval();
        int64_t rand = randomInInterval(interval);
        m_out.addArrayAssignment(array_name, i_val, rand);
      }
    }
    if (valid_model) {
//    TODO remove_aux_arrays(m_out, aux_list)
      return m_out.toString();
    }
  }
}

std::string MEGASampler::get_random_sample_from_int_intervals(
    const capnpIntervalMap& intervalmap) {
  std::string sample_string;
  for (auto varinterval : intervalmap) {
    std::string varname = varinterval.getVariable().cStr();
    const auto& interval = varinterval.getInterval();
    sample_string += varname;
    sample_string += ":";
    int64_t randNum = randomInInterval(interval);
    sample_string += std::to_string(randNum);
    sample_string += ";";
  }
  return sample_string;
}

static inline z3::expr combine_expr(const z3::expr& base, const z3::expr& arg) {
  if (base) return base && arg;
  return arg;
}

void MEGASampler::add_soft_constraint_from_intervals(
    const capnpIntervalMap& intervals,
    const std::vector<arrayAccessData>& index_vec) {
  z3::expr expr(c);
  for (auto interval : intervals) {
    std::string varsort = interval.getVarsort().cStr();
    if (varsort == "int") {
      const auto var = c.int_const(interval.getVariable().cStr());
      if (!interval.getInterval().getIslowminf()) {
        const auto low = c.int_val(interval.getInterval().getLow());
        expr = combine_expr(expr, var >= low);
      }
      if (!interval.getInterval().getIshighinf()) {
        const auto high = c.int_val(interval.getInterval().getHigh());
        expr = combine_expr(expr, var <= high);
      }
    }
  }
  z3::sort int_sort = c.int_sort();
  z3::sort array_sort = c.array_sort(int_sort, int_sort);
  for (const auto& access_data : index_vec) {
    std::string array_name = access_data.entryInCapnpMap.getVariable().cStr();
    z3::expr arr = c.constant(array_name.c_str(), array_sort);
    z3::expr select_e = z3::select(arr, access_data.indexExpr);
    if (!access_data.entryInCapnpMap.getInterval().getIslowminf()) {
      const auto low =
          c.int_val(access_data.entryInCapnpMap.getInterval().getLow());
      expr = combine_expr(expr, select_e >= low);
    }
    if (!access_data.entryInCapnpMap.getInterval().getIshighinf()) {
      const auto high =
          c.int_val(access_data.entryInCapnpMap.getInterval().getHigh());
      expr = combine_expr(expr, select_e <= high);
    }
  }
  if (debug) std::cout << "blocking constraint: " << expr.to_string() << "\n";
  opt.add_soft(!expr, 1);
}

z3::expr MEGASampler::deserialise_expr(const std::string& str) {
  auto constraints = c.parse_string(str.c_str());
  assert(constraints.size() == 1);
  assert(constraints[0].is_eq());
  return constraints[0].arg(0);
}
