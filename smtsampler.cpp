#include "smtsampler.h"

#include <cinttypes>
#include <climits>
#include <cstring>

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
    // TODO: Handle array case, orig:smtsampler.cpp:408
    if (v.range().is_array()) {
      assert(m_string[pos] == '[');
      ++pos;
      unsigned long long num = atoll(m_string.c_str() + pos);  // array size
      pos = m_string.find(';', pos) + 1;
      z3::expr def = value(m_string.c_str() + pos);
      pos = m_string.find(';', pos) + 1;

      for (unsigned long long i = 0; i < num; ++i) {
        z3::expr arg = value(m_string.c_str() + pos);
        pos = m_string.find(';', pos) + 1;

        z3::expr val = value(m_string.c_str() + pos);
        pos = m_string.find(';', pos) + 1;

        add_constraints(z3::select(v(), arg), val, -1);
      }
      assert(m_string.c_str()[pos] == ']');
      ++pos;
    } else if (v.is_const()) {
      z3::expr a = value(m_string.c_str() + pos, v.range());
      pos = m_string.find(';', pos) + 1;
      add_constraints(v(), a, count);
    } else {
      // TODO: Handle uninterpreted function case
      assert(false);
    }
  }
  if (debug) {
    std::cout << "Collected constraints: ";
    for (auto constraint : constraints) {
      std::cout << constraint << " ";
    }
    std::cout << "\n";
  }
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
        if (debug) std::cout << "mutation: " << sample_to_file << "\n";
        save_and_output_sample_if_unique(sample_to_file);  // todo: check format
        flips += 1;
      } else if (debug) {
        std::cout << "repeated\n";
      }
    } else if (res == z3::unsat) {
      if (debug) std::cout << "unsat\n";
      if (cons_to_ind[count].first >= 0) {
        unsat_ind[cons_to_ind[count].first].insert(cons_to_ind[count].second);
        ++unsat_ind_count;
      }
    }

    opt.pop();
    solver.pop();
    // print === as a progress bar (80 '=' to mark 100% of constraints flipped)
    if (debug) {
      double new_progress =
          80.0 * (double)((count + 1)) / (double)(constraints.size());
      while (progress < new_progress) {
        ++progress;
        std::cout << '=' << std::flush;
      }
    }
  }
  if (debug) std::cout << '\n';
}

std::string SMTSampler::combine_function(std::string const &str_a,
                                         std::string const &str_b,
                                         std::string const &str_c,
                                         size_t &pos_a, size_t &pos_b,
                                         size_t &pos_c, int arity, z3::sort s) {
  std::stringstream ss;
  std::unordered_map<std::string, SMTSampler::Triple> values;
  if (debug) std::cerr << "combine_function" << s << '\n';
  const std::string def_a = parse_function(str_a, pos_a, arity, values, 0);
  const std::string def_b = parse_function(str_b, pos_b, arity, values, 1);
  const std::string def_c = parse_function(str_c, pos_c, arity, values, 2);

  ss << (arity == 0 ? '[' : '(');
  ss << std::to_string(values.size()) << ';';
  ss << std::to_string(
            combine_mutations(stoll(def_a), stoll(def_b), stoll(def_c)))
     << ';';
  for (const auto &value : values) {
    std::string val_a = value.second.a[0];
    if (val_a.empty()) val_a = def_a;
    std::string val_b = value.second.a[1];
    if (val_b.empty()) val_b = def_b;
    std::string val_c = value.second.a[2];
    if (val_c.empty()) val_c = def_c;
    ss << value.first;
    ss << std::to_string(
              combine_mutations(stoll(val_a), stoll(val_b), stoll(val_c)))
       << ';';
  }
  ss << (arity == 0 ? ']' : ')');
  return ss.str();
}

std::string SMTSampler::parse_function(
    std::string const &m_string, size_t &pos, int arity,
    std::unordered_map<std::string, SMTSampler::Triple> &values, int index) {
  size_t start;
  bool is_array = false;
  if (arity == 0) {
    is_array = true;
    arity = 1;
  }
  assert(m_string[pos] == (is_array ? '[' : '('));
  ++pos;
  int num = atoi(m_string.c_str() + pos);
  pos = m_string.find(';', pos) + 1;

  start = pos;
  pos = m_string.find(';', pos) + 1;
  const std::string def = m_string.substr(start, pos - start);

  for (int i = 0; i < num; ++i) {
    start = pos;
    for (int k = 0; k < arity; ++k) {
      pos = m_string.find(';', pos) + 1;
    }
    std::string args = m_string.substr(start, pos - start);
    start = pos;
    pos = m_string.find(';', pos) + 1;
    values[args].a[index] = m_string.substr(start, pos - start);
  }
  assert(m_string[pos] == (is_array ? ']' : ')'));
  ++pos;
  return def;
}

void SMTSampler::find_combined_solutions(
    std::unordered_set<std::string> &mutations, const std::string &a_string) {
  std::vector<std::string> initial(mutations.begin(), mutations.end());
  std::vector<std::string> sigma = initial;
  for (int k = 2; k <= 6; ++k) {
    is_time_limit_reached();
    if (debug) std::cout << "Combining " << k << " mutations\n";
    std::vector<std::string> new_sigma;
    int all_new = 0;
    int good = 0;
    for (std::string b_string : sigma) {
      for (std::string c_string : initial) {
        is_time_limit_reached();
        if (debug)
          std::cout << "combining: " << b_string << " and " << c_string
                    << " (orig is:" << a_string << ")\n";
        size_t pos_a = 0;
        size_t pos_b = 0;
        size_t pos_c = 0;
        std::string candidate;
        for (z3::func_decl &w : ind) {
          if (w.range().is_array()) {
            const int arity = 0;                   // all we support?
            z3::sort s = w.range().array_range();  // should always be int
            candidate += combine_function(a_string, b_string, c_string, pos_a,
                                          pos_b, pos_c, arity, s);
          } else if (w.is_const()) {
            assert_is_int_var(w);
            const long long val_a = ll_value(a_string.c_str() + pos_a);
            const long long val_b = ll_value(b_string.c_str() + pos_b);
            const long long val_c = ll_value(c_string.c_str() + pos_c);
            const int num = combine_mutations(val_a, val_b, val_c);
            pos_a = a_string.find(';', pos_a) + 1;
            pos_b = b_string.find(';', pos_b) + 1;
            pos_c = c_string.find(';', pos_c) + 1;
            candidate += std::to_string(num) + ';';
          } else {
            // Uninterpreted function case
            assert(false);
          }
        }
        if (debug) std::cout << "candidate: " << candidate << "\n";
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
        } else if (debug) {
          std::cout << "repeated candidate\n";
        }
      }
    }
    double accuracy = (double)(good) / (double)(all_new);
    if (debug)
      std::cout << "Valid: " << good << " / " << all_new << " = " << accuracy
                << '\n';
    //		print_stats();
    if (all_new == 0 || accuracy < 0.1) break;

    sigma = new_sigma;
  }
}

void SMTSampler::do_epoch(const z3::model &m) {
  is_time_limit_reached();

  if (debug) std::cout << "SMTSAMPLER: do epoch\n";
  if (debug) std::cout << "model is: " << m << "\n";

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
  std::stringstream ss;
  for (z3::func_decl &v : _ind) {
    if (v.range().is_array()) {
      // case array
      z3::expr e = m.get_const_interp(v);
      const Z3_func_decl as_array = Z3_get_as_array_func_decl(c, e);
      if (as_array) {  // is this an "as_array" cmd
        z3::func_interp f = m.get_func_interp(to_func_decl(c, as_array));
        ss << '[' << std::to_string(f.num_entries()) << ';';
        ss << f.else_value() << ';';
        for (unsigned int i = 0; i < f.num_entries(); ++i) {
          ss << f.entry(i).arg(0) << ';';
          ss << f.entry(i).value() << ';';
        }
        ss << ']';
      } else {  // this is a list of stores
        std::vector<std::string> args;
        std::vector<std::string> values;
        while (e.decl().name().str() == "store") {
          if (debug) {
            std::cerr << "model_string found store: " << e << '\n';
          }
          std::string arg = std::to_string(e.arg(1));
          // TODO: seems inefficient, use a set?
          if (std::find(args.begin(), args.end(), arg) != args.end()) {
            e = e.arg(0);
            continue;
          }
          args.push_back(arg);
          values.push_back(std::to_string(e.arg(2)));
          e = e.arg(0);  // go to inner cmd
        }
        ss << '[' << std::to_string(args.size()) << ';';
        ss << e.arg(0) << ';';
        for (int i = args.size() - 1; i >= 0; --i) {
          ss << args[i] << ';' << values[i] << ';';
        }
        ss << ']';
      }
    } else if (v.is_const()) {
      // case const, i.e., int or bool sorts
      z3::expr b = m.get_const_interp(v);
      Z3_ast ast = b;
      assert(ast);  // model should have an interpretation for all variables
      switch (v.range().sort_kind()) {
        case Z3_INT_SORT:
          ss << b << ';';
          break;
        case Z3_BOOL_SORT:
          ss << std::to_string(b.bool_value() == Z3_L_TRUE) << ';';
          break;
        default:
          assert_is_int_var(v);
      }
    } else {
      // case uninterpreted functions
      assert(false);
    }
  }
  return ss.str();
}

z3::expr SMTSampler::value(char const *n) {
  return c.int_val((int64_t)ll_value(n));
}

z3::expr SMTSampler::value(char const *n, z3::sort s) {
  switch (s.sort_kind()) {
    case Z3_INT_SORT:
      return value(n);
    case Z3_BOOL_SORT:
      return c.bool_val(ll_value(n) == 1);
    default:
      assert(false);
  }
}

// (exp == val) is added as soft constraint (to opt)
void SMTSampler::add_constraints(z3::expr exp, z3::expr val, int count) {
  assert(val.get_sort().sort_kind() == Z3_INT_SORT ||
         val.get_sort().sort_kind() == Z3_BOOL_SORT);
  all_ind_count += (count >= 0);
  cons_to_ind.emplace_back(count, 0);
  constraints.push_back(exp == val);
  //    std::vector<z3::expr> soft;
  //    soft_constraints.push_back(soft);
  assert_soft(exp == val);
}

static inline long long add_safe(long long a, long long b) {
  long long ret;
  if (!__builtin_add_overflow(a, b, &ret)) return ret;
  return (a < 0) ? LLONG_MIN : LLONG_MAX;
}

int SMTSampler::combine_mutations(long long val_orig, long long val_b,
                                  long long val_c) {
  return add_safe(val_orig, add_safe(val_b, val_c));
}

z3::model SMTSampler::gen_model(const std::string &candidate,
                                std::vector<z3::func_decl> &_ind) {
  z3::model m(c);
  size_t pos = 0;
  for (z3::func_decl &v : _ind) {
    if (v.range().is_array()) {
      assert(candidate[pos] == '[');
      ++pos;

      int num = atoi(candidate.c_str() + pos);
      pos = candidate.find(';', pos) + 1;

      z3::expr def = value(candidate.c_str() + pos);
      pos = candidate.find(';', pos) + 1;

      Z3_sort domain_sort[1] = {v.range().array_domain()};
      Z3_func_decl cfd = Z3_mk_fresh_func_decl(c, "k", 1, domain_sort,
                                               v.range().array_range());

      z3::func_decl fd(c, cfd);
      z3::func_interp f = m.add_func_interp(fd, def);

      for (int i = 0; i < num; ++i) {
        z3::expr_vector args(c);
        args.push_back(value(candidate.c_str() + pos));
        pos = candidate.find(';', pos) + 1;

        z3::expr val = value(candidate.c_str() + pos);
        f.add_entry(args, val);
        pos = candidate.find(';', pos) + 1;
      }
      z3::expr array = as_array(fd);
      m.add_const_interp(v, array);
      assert(candidate[pos] == ']');
      ++pos;
    } else if (v.is_const()) {
      z3::expr a = value(candidate.c_str() + pos, v.range());
      pos = candidate.find(';', pos) + 1;
      m.add_const_interp(v, a);
    } else {
      // uninterpreted function case
      assert(false);
    }
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
