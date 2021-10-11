#include "smtsampler.h"

#include <climits>
#include <cinttypes>

SMTSampler::SMTSampler(std::string _input, std::string _output_dir,
                       int _max_samples, double _max_time,
                       int _max_epoch_samples, double _max_epoch_time,
                       int _strategy, bool _json, bool _blocking)
    : Sampler(_input, _output_dir, _max_samples, _max_time, _max_epoch_samples,
              _max_epoch_time, _strategy, _json, _blocking),
      strategy(_strategy) {
  initialize_solvers();
  //  if (!convert) {
  ind = variables;
  //  }
  std::cout << "starting SMTSampler" << std::endl;
}

void SMTSampler::calculate_constraints(const std::string &m_string) {
  size_t pos = 0;
  for (size_t count = 0; count < ind.size(); ++count) {
    z3::func_decl &v = ind[count];
    assert_is_int_var(v);
    z3::expr a = value(m_string.c_str() + pos);
    pos = m_string.find(';', pos) + 1;
    add_constraints(v(), a, count);
  }
  std::cout << "Collected constraints: ";
  for (auto constraint : constraints) {
    std::cout << constraint << " ";
  }
  std::cout << "\n";
}

void SMTSampler::find_neighboring_solutions(
    std::unordered_set<std::string> &mutations) {
  // STEP 2: mutate constraints to get Sigma_1 (solutions of distance 1)
  struct timespec etime;
  clock_gettime(CLOCK_REALTIME, &etime);
  double start_epoch = duration(&timer_start_times["total"], &etime);
  int calls = 0;
  int progress = 0;
  for (size_t count = 0; count < constraints.size(); ++count) {
    is_time_limit_reached();
    // todo uncomment? is this necessary?
    //		auto u = unsat_ind.find(cons_to_ind[count].first);
    //		if (u != unsat_ind.end()
    //				&& u->second.find(cons_to_ind[count].second)
    //						!= u->second.end()) {
    //			continue;
    //		}
    z3::expr &cond = constraints[count];
    opt.push();
    solver.push();
    opt.add(!cond);
    solver.add(!cond);
    // probably redundant: soft seems to always be empty
    //		for (z3::expr &soft : soft_constraints[count]) {
    //			assert_soft(soft);
    //		}
    struct timespec end;
    clock_gettime(CLOCK_REALTIME, &end);
    double elapsed = duration(&timer_start_times["total"], &end);
    double cost = calls ? (elapsed - start_epoch) / calls : 0.0;
    cost *= constraints.size() - count;
    if (max_time / 3.0 + start_epoch > max_time && elapsed + cost > max_time) {
      std::cout << "Stopping: slow\n";
      finish();
    }
    z3::check_result res = z3::unknown;
    if (cost * rand() <= (max_time / 3.0 + start_epoch - elapsed) * RAND_MAX) {
      res = solve("epoch");
      ++calls;
    }
    if (res == z3::sat) {
      std::string new_string = model_string(model, ind);
      total_samples++;
      if (mutations.find(new_string) == mutations.end()) {
        mutations.insert(new_string);
        std::string sample_to_file = model_to_string(model);
        std::cout << "mutation: " << sample_to_file << "\n";
        save_and_output_sample_if_unique(sample_to_file);  // todo: check format
        flips += 1;
      } else {
        std::cout << "repeated\n";
      }
    } else if (res == z3::unsat) {
      std::cout << "unsat\n";
      if (cons_to_ind[count].first >= 0) {
        unsat_ind[cons_to_ind[count].first].insert(cons_to_ind[count].second);
        ++unsat_ind_count;
      }
    }

    opt.pop();
    solver.pop();
    // print === as a progress bar (80 '=' to mark 100% of constraints flipped)
    double new_progress =
        80.0 * (double)((count + 1)) / (double)(constraints.size());
    while (progress < new_progress) {
      ++progress;
      std::cout << '=' << std::flush;
    }
  }
  std::cout << '\n';
}

void SMTSampler::find_combined_solutions(
    std::unordered_set<std::string> &mutations, const std::string &a_string) {
  std::vector<std::string> initial(mutations.begin(), mutations.end());
  std::vector<std::string> sigma = initial;
  for (int k = 2; k <= 6; ++k) {
    is_time_limit_reached();
    std::cout << "Combining " << k << " mutations\n";
    std::vector<std::string> new_sigma;
    int all_new = 0;
    int good = 0;
    for (std::string b_string : sigma) {
      for (std::string c_string : initial) {
        is_time_limit_reached();
        std::cout << "combining: " << b_string << " and " << c_string
                  << " (orig is:" << a_string << ")\n";
        size_t pos_a = 0;
        size_t pos_b = 0;
        size_t pos_c = 0;
        std::string candidate;
        for (z3::func_decl &w : ind) {
          assert_is_int_var(w);
          long long val_a = ll_value(a_string.c_str() + pos_a);
          long long val_b = ll_value(b_string.c_str() + pos_b);
          long long val_c = ll_value(c_string.c_str() + pos_c);
          int num = combine_mutations(val_a, val_b, val_c);
          pos_a = a_string.find(';', pos_a) + 1;
          pos_b = b_string.find(';', pos_b) + 1;
          pos_c = c_string.find(';', pos_c) + 1;
          candidate += std::to_string(num) + ';';
        }
        std::cout << "candidate: " << candidate << "\n";
        total_samples++;
        if (mutations.find(candidate) == mutations.end() &&
            strcmp(candidate.c_str(), a_string.c_str()) != 0) {
          mutations.insert(candidate);
          z3::model m = gen_model(candidate, variables);
          z3::expr b = m.eval(original_formula, true);
          bool valid = b.bool_value() == Z3_L_TRUE;
          ++all_new;
          if (valid) {
            std::string output = model_to_string(m);
            save_and_output_sample_if_unique(output);
            ++good;
            new_sigma.push_back(candidate);
          }
        } else {
          std::cout << "repeated candidate\n";
        }
      }
    }
    double accuracy = (double)(good) / (double)(all_new);
    std::cout << "Valid: " << good << " / " << all_new << " = " << accuracy
              << '\n';
    //		print_stats();
    if (all_new == 0 || accuracy < 0.1) break;

    sigma = new_sigma;
  }
}

void SMTSampler::do_epoch(const z3::model &m) {
  is_time_limit_reached();

  std::cout << "SMTSAMPLER: do epoch\n";
  std::cout << "model is: " << m << "\n";

  std::unordered_set<std::string> mutations;
  std::string m_string = model_string(m, ind);

  opt.push();
  solver.push();

  constraints.clear();
  soft_constraints.clear();
  cons_to_ind.clear();
  all_ind_count = 0;

  // STEP 1: calculate constraints based on model
  calculate_constraints(m_string);
  is_time_limit_reached();
  // STEP 2: mutate constraints to get Sigma_1 (solutions of distance 1)
  find_neighboring_solutions(mutations);
  is_time_limit_reached();
  // STEP 3: combine mutations to get Sigma_2...Sigma_6 (solutions of distance
  // 2-6)
  find_combined_solutions(mutations, m_string);
  is_time_limit_reached();

  opt.pop();
  solver.pop();
}

std::string SMTSampler::model_string(z3::model m,
                                     std::vector<z3::func_decl> _ind) {
  std::string s;
  for (z3::func_decl &v : _ind) {
    assert_is_int_var(v);
    z3::expr b = m.get_const_interp(v);
    Z3_ast ast = b;
    assert(ast);  // model should have an interpretation for all variables
    std::stringstream ss;
    ss << b;
    s += ss.str() + ';';
  }
  return s;
}

z3::expr SMTSampler::value(char const *n) {
  return c.int_val((int64_t) ll_value(n));
}

// (exp == val) is added as soft constraint (to opt)
void SMTSampler::add_constraints(z3::expr exp, z3::expr val, int count) {
  assert(val.get_sort().sort_kind() == Z3_INT_SORT);
  all_ind_count += (count >= 0);
  cons_to_ind.emplace_back(count, 0);
  constraints.push_back(exp == val);
  //    std::vector<z3::expr> soft;
  //    soft_constraints.push_back(soft);
  assert_soft(exp == val);
}

inline long long add_safe(long long a, long long b) {
  if (b >= 0) {
    return a > INT_MAX - b ? INT_MAX : a + b;
  } else { // b < 0
    return a < INT_MIN - b ? INT_MIN : a + b;
  }
}

int SMTSampler::combine_mutations(long long val_orig, long long val_b, long long val_c) {
  return add_safe(val_orig, add_safe(val_b, val_c));
}

z3::model SMTSampler::gen_model(const std::string &candidate,
                                std::vector<z3::func_decl> &_ind) {
  z3::model m(c);
  size_t pos = 0;
  for (z3::func_decl &v : _ind) {
    assert_is_int_var(v);
    z3::expr a = value(candidate.c_str() + pos);
    pos = candidate.find(';', pos) + 1;
    m.add_const_interp(v, a);
  }
  return m;
}

void SMTSampler::assert_is_int_var(const z3::func_decl &v) {
  assert(v.is_const() and v.range().sort_kind() == Z3_INT_SORT);
}

long long SMTSampler::ll_value(char const *n) {
  assert(n);
  if (n[0] == '(') {  // if n is negative we need to remove the brackets
    assert(n[1] == '-' && n[2] == ' ');
    return -atoll(n + 3);
  }
  return atoll(n);
}

void SMTSampler::finish() {
  json_output["method name"] = "smtsampler";
  Sampler::finish();
}
