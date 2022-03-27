#include "megasampler.h"

#include <capnp/serialize.h>

#include <cinttypes>
#include <cstdint>
#include <iostream>
#include <random>
#include <set>

#include "model.h"
#include "pythonfuncs.h"
#include "strengthen.capnp.h"

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

void MEGASampler::register_store_eq(z3::expr& f){
  if (is_array_eq(f)) {
    const z3::expr& left_a = f.arg(0);
    const z3::expr& right_a = f.arg(1);
    storeEquality st_eq(c);
    st_eq.store_id = f.id();
    save_store_index_and_value(left_a, st_eq.a_indices, st_eq.a_values, st_eq.a);
    save_store_index_and_value(right_a, st_eq.b_indices, st_eq.b_values, st_eq.b);
    store_eqs.push_back(st_eq);
  } else {
    for (auto child : f){
      register_store_eq(child);
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

void MEGASampler::eliminate_eq_of_different_arrays(){
    // looking for an expr e of the form store(..(store(a,i,t_i))=store(..(store(b,j,s_j)) where a and b are distinct
    z3::expr a(c);
    z3::expr b(c);
    z3::expr e(c);
    bool res = find_eq_of_different_arrays(original_formula, a, b, e);
    while (res) {
//        std::cout << "found eq of different arays: " << e.to_string() << "\n";
//        std::cout << "first array name: " << a.to_string() << "\n";
//        std::cout << "second array name: " << b.to_string() << "\n";
        // declare auxiliary array variable aux_a
        std::string aux_a_name = "aux_a_" + std::to_string(aux_array_index);
        aux_array_index++;
        z3::expr aux_a = c.constant(aux_a_name.c_str(), c.array_sort(c.int_sort(),c.int_sort()));
        // record name substitution for future model reconstruction
        array_renaming_vec.push_back(arrayRenaming(aux_a_name, a.to_string(), b.to_string()));
        // substitute a and b for a_aux in e to form e'
        z3::expr_vector src_exprs(c), dst_exprs(c);
        src_exprs.push_back(a);
        src_exprs.push_back(b);
        dst_exprs.push_back(aux_a);
        dst_exprs.push_back(aux_a);
        z3::expr e_prime = e.substitute(src_exprs, dst_exprs);
//        std::cout << "e' is: " << e_prime.to_string() << "\n";
        // substitute e for e' in the formula
        z3::expr_vector src_exprs2(c), dst_exprs2(c);
        src_exprs2.push_back(e);
        dst_exprs2.push_back(e_prime);
        original_formula = original_formula.substitute(src_exprs2, dst_exprs2);
//        std::cout << "formula after e to e' substitution: " << original_formula.to_string() << "\n";
        // custom-substitute a for a_aux and t_i for select(a,t_i) in left_array, to form a'. same for b
        z3::expr left_array = e.arg(0);
        z3::expr a_prime = store_substitute(left_array, a, aux_a);
//        std::cout << "a' is: " << a_prime.to_string() << "\n";
        z3::expr right_array = e.arg(1);
        z3::expr b_prime = store_substitute(right_array, b, aux_a);
//        std::cout << "b' is: " << b_prime.to_string() << "\n";
        // substitute a for a' and b for b' in the formula
        src_exprs = z3::expr_vector(c);
        dst_exprs = z3::expr_vector(c);
        src_exprs.push_back(a);
        dst_exprs.push_back(a_prime);
        src_exprs.push_back(b);
        dst_exprs.push_back(b_prime);
        original_formula = original_formula.substitute(src_exprs, dst_exprs);
//        std::cout << "formula after a,b to a',b' substitution: " << original_formula.to_string() << "\n";
        // find another eq (loop progress)
        res = find_eq_of_different_arrays(original_formula, a, b, e);
    }
    if (debug) {
        std::cout << "array_renaming_vec: ";
        for (auto ar: array_renaming_vec) {
            std::cout << ar.aux_name << ":(" << ar.a_name << "," << ar.b_name << ")   ";
        }
        std::cout << "\n";
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

  register_store_eq(original_formula);
  for (auto store_eq : store_eqs){
    std::cout << "\n";
    std::cout << store_eq.toString();
    std::cout << "\n";
  }

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

static void remove_or(z3::expr& formula, const z3::model& m, std::vector<z3::expr>& res){
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

void MEGASampler::remove_array_equalities(std::vector<z3::expr>& conjuncts){
  for (auto it = conjuncts.begin(); it != conjuncts.end(); it++){
    const z3::expr& conjunct = *it;
    if (is_array_eq(conjunct)){
      // remove it from imlicant_conjuncts
      conjuncts.erase(it);
      // find store_eq in store_eqs
      // build a list of tuples (index_val, index_e, value_e, in_left_array)
      // sort this list according to index_val
      // add index relationship conatraints
      // add value constraints for store indices
      // replace selects over indices not in I or J inside implicant_conjuncts
    }
  }
  std::cout << "after removing array eqs: ";
  for (auto conjunct : conjuncts){
    std::cout << conjunct.to_string() << ",";
  }
  std::cout << "\n";
}

void MEGASampler::do_epoch(const z3::model& m) {
  is_time_limit_reached();

  std::vector<z3::expr> implicant_conjuncts_vec;
  remove_or(simpl_formula, m, implicant_conjuncts_vec);
  if (debug) {
    std::cout << "after remove or: ";
    for (auto conj: implicant_conjuncts_vec){
      assert(conj);
      std::cout << conj.to_string() << ",";
    }
    std::cout << "\n";
  }
  remove_array_equalities(implicant_conjuncts_vec);

  z3::expr_vector implicant_conjuncts(c);
  for (auto conj: implicant_conjuncts_vec){
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
