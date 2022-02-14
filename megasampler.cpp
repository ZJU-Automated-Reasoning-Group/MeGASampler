#include "megasampler.h"

#include <capnp/serialize.h>

#include <cinttypes>
#include <cstdint>
#include <iostream>
#include <random>

#include "pythonfuncs.h"
#include "strengthen.capnp.h"
#include "model.h"

static inline bool check_if_in_interval(int64_t val, const MEGASampler::capnpInterval& interval){
    return (val >= interval.getLow() && val <= interval.getHigh());
}

static int count_selects(const z3::expr & e){
    if (!e.is_app()) return 0;
    int count = (e.decl().decl_kind() == Z3_OP_SELECT);
    for (unsigned int i=0; i < e.num_args(); i++){
        count += count_selects(e.arg(i));
    }
    return count;
}

MEGASampler::MEGASampler(std::string _input, std::string _output_dir,
                         int _max_samples, double _max_time,
                         int _max_epoch_samples, double _max_epoch_time,
                         int _strategy, bool _json, bool _blocking)
    : Sampler(_input, _output_dir, _max_samples, _max_time, _max_epoch_samples,
              _max_epoch_time, _strategy, _json, _blocking),
      simpl_formula(c) {
  initialize_solvers();
  std::cout << "starting MEGA" << std::endl;
}

void MEGASampler::do_epoch(const z3::model& m) {
  is_time_limit_reached();
  struct buflen ret = call_strengthen(original_formula, m, has_arrays, debug);
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
  std::sort(index_vec.begin(),index_vec.end());
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
    const capnp::List<StrengthenResult::VarInterval>::Reader& intervalmap, const std::vector<arrayAccessData>& index_vec) {
  uint64_t coeff = 1;
  for (auto imap : intervalmap) {
    const auto& i = imap.getInterval();
    if (i.getIslowminf() || i.getIshighinf()) {
      coeff += 32;
      continue;
    }
    coeff = safe_mul(coeff, ilog2(1 + ilog2(1 + i.getHigh() - i.getLow())));
  }
  if (use_blocking) coeff = safe_mul(coeff, intervalmap.size());
  const uint64_t MAX_ROUNDS = std::max(use_blocking ? 50UL : 10UL, coeff);
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
      if (has_arrays){
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

int64_t randomInInterval(const MEGASampler::capnpInterval & interval){
    int64_t low = interval.getLow();
    int64_t high = interval.getHigh();
    std::mt19937 rng(std::random_device{}());
    std::uniform_int_distribution<int64_t> gen(low, high);  // uniform, unbiased
    return gen(rng);
}

std::string MEGASampler::get_random_sample_from_array_intervals(
        const capnpIntervalMap& intervalmap, const std::vector<arrayAccessData>& indexvec){
    while(true) { //TODO some heuristic for early termination in case we keep getting clashes?
        Model m_out;
        bool valid_model = true;
        for (auto varinterval: intervalmap) {
            std::string varsort = varinterval.getVarsort().cStr();
            if (varsort == "int") {
                std::string varname = varinterval.getVariable().cStr();
                const auto &interval = varinterval.getInterval();
                int64_t rand = randomInInterval(interval);
                bool res = m_out.addIntAssignment(varname, rand);
                assert(res);
            }
        }
//        std::cout << "model after int assignment:\n" << m_out.toString() << "\n";
        for (auto it = indexvec.begin(); it < indexvec.end(); it++) {
            int64_t i_val;
            z3::expr index_expr = it->indexExpr;
            auto index_res = m_out.evalIntExpr(index_expr, false, true);
            assert (index_res.second);
            i_val = index_res.first;
            std::string array_name = it->entryInCapnpMap.getVariable().cStr();
            auto res = m_out.evalArrayVar(array_name, i_val);
            if (res.second) {
                valid_model = check_if_in_interval(res.first, it->entryInCapnpMap.getInterval());
                if (!valid_model) break;
            } else {
                const auto &interval = it->entryInCapnpMap.getInterval();
                int64_t rand = randomInInterval(interval);
                m_out.addArrayAssignment(array_name, i_val, rand);
            }
        }
        if (valid_model) {
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
    const capnpIntervalMap& intervals, const std::vector<arrayAccessData>& index_vec) {
  z3::expr expr(c);
  for (auto interval : intervals) {
    std::string varsort =  interval.getVarsort().cStr();
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
  z3::sort array_sort = c.array_sort(int_sort,int_sort);
  for (const auto & access_data : index_vec){
      std::string array_name = access_data.entryInCapnpMap.getVariable().cStr();
      z3::expr arr = c.constant(array_name.c_str(), array_sort);
      z3::expr select_e = z3::select(arr, access_data.indexExpr);
      if (!access_data.entryInCapnpMap.getInterval().getIslowminf()) {
          const auto low = c.int_val(access_data.entryInCapnpMap.getInterval().getLow());
          expr = combine_expr(expr, select_e >= low);
      }
      if (!access_data.entryInCapnpMap.getInterval().getIshighinf()) {
          const auto high = c.int_val(access_data.entryInCapnpMap.getInterval().getHigh());
          expr = combine_expr(expr, select_e <= high);
      }
  }
  if (debug) std::cout << "blocking constraint: " << expr.to_string() << "\n";
  opt.add_soft(!expr, 1);
}

z3::expr MEGASampler::deserialise_expr(const std::string & str){
    auto constraints = c.parse_string(str.c_str());
    assert(constraints.size() == 1);
    assert(constraints[0].is_eq());
    return constraints[0].arg(0);
}