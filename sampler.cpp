#include "sampler.h"

#include <filesystem>
#include <fstream>

Sampler::Sampler(z3::context *_c, const std::string &_input,
                 const std::string &_output_dir,
                 const MeGA::SamplerConfig &config)
    : c(*_c),
      original_formula(c),
      params(c),
      model(c),
      opt(c),
      solver(c),
      input_filename(_input),
      output_dir(_output_dir),
      config(config) {
  z3::set_param("rewriter.expand_select_store", "true");
  // Parallel makes it ignore the timeout :(
  // z3::set_param("parallel.enable", "true");
  params.set(":timeout", 50000u);
  opt.set(params);
  solver.set(params);

  parse_formula(_input);

  compute_and_print_formula_stats();

  const std::filesystem::path input_path = _input;
  const std::filesystem::path output_path = _output_dir;
  if (!std::filesystem::exists(output_path)) {
    std::filesystem::create_directories(output_path);
  }
  if (!std::filesystem::is_directory(output_path)) {
    std::cout << "Output directory is not a directory. Exiting.\n";
    failure_cause = "Output directory exists and is not a directory.";
    safe_exit(1);
  }
  const std::string output_base =
      (output_path / input_path.filename()).string();
  json_filename = output_base + ".json";
  if (!config.no_write)
    results_file.open(output_base + ".samples");

  if (num_bv > 0 || num_uf > 0 || num_reals > 0) {
    std::cout << "Unsupported sort in formula. Exiting.\n";
    failure_cause = "Unsupported sort in formula.";
    safe_exit(1);
  }

  if (num_arrays > 0) {
    has_arrays = true;
  }

  if (false && num_bools > 0) {
    // Are boolean vars actually fine ... ?
    std::cout << "Currently not supporting boolean vars in formula.\n";
    failure_cause = "Bool vars in formula.";
    safe_exit(1);
  }
}

void Sampler::initialize_solvers() {
  opt.add(original_formula);  // adds formula as hard constraint to optimization
                              // solver (no weight specified for it)
  solver.add(original_formula);  // adds formula as constraint to normal solver
  if (config.blocking) solver.push();
}

double Sampler::duration(struct timespec *a, struct timespec *b) {
  return (b->tv_sec - a->tv_sec) + 1.0e-9 * (b->tv_nsec - a->tv_nsec);
}

double Sampler::get_elapsed_time() {
  return elapsed_time_from(timer_start_times["total"]);
}

double Sampler::get_epoch_elapsed_time() {
  return elapsed_time_from(timer_start_times["epoch"]);
}

double Sampler::get_time_left(const std::string &t) {
  double ret = max_times[t] - elapsed_time_from(timer_start_times[t]);
  ret = (ret >= 0.0) ? ret : 1.0;
  if ("total" == t) {
    return ret;
  }
  // Never return more than the total time left
  return std::min(ret, get_time_left("total"));
}

double Sampler::elapsed_time_from(struct timespec start) {
  struct timespec end;
  clock_gettime(CLOCK_REALTIME, &end);
  return duration(&start, &end);
}

void Sampler::parse_formula(const std::string &input) {
  std::cout << "Parsing input file: " << input << '\n';
  z3::expr_vector formulas =
      c.parse_file(input.c_str());  // bat: reads smt2 file
  std::cout << "Number of formulas in file: " << formulas.size() << '\n';
  z3::expr formula = mk_and(formulas);
  Z3_ast ast = formula;
  if (ast == NULL) {
    std::cerr << "Could not read input formula." << std::endl;
    failure_cause = "Could not read input formula.";
    safe_exit(1);
  }
  original_formula = formula;
  if (config.debug)
    std::cout << "Read formula: " << original_formula << std::endl;
}

void Sampler::check_if_satisfiable() {
  z3::check_result res = solve("total");  // will try to solve the formula and
                                          // put model in model variable
  if (res == z3::unsat) {
    sat_result = "unsat";
    std::cout << "Formula is unsat\n";
    safe_exit(0);
  } else if (res == z3::unknown) {
    sat_result = "unknown";
    std::cout << "Solver returned unknown\n";
    safe_exit(0);
  } else {
    sat_result = "sat";
    std::cout << "Formula is satisfiable\n";
  }
}

z3::check_result Sampler::solve(const std::string &timer_category,
                                bool solve_opt) {
  z3::check_result res = z3::unknown;
  if (solve_opt) {
    try {
      max_smt_calls++;
      const unsigned timeout = std::min<unsigned>(
          1000 * 60 * 5,
          static_cast<unsigned>(800 * get_time_left(timer_category)));
      params.set(":timeout", timeout);
      params.set("timeout", timeout);

      opt.set(params);
      res = opt.check();  // bat: first, solve a MAX-SMT instance
    } catch (const z3::exception &except) {
      std::cout << "Exception: " << except << "\n";
      // TODO exception "canceled" can be thrown when Timeout is reached
      failure_cause = "MAX-SMT exception";
      safe_exit(1);
    }
  }
  if (res == z3::sat) {
    model = opt.get_model();
  } else if (res == z3::unknown) {
    if (solve_opt) std::cout << "MAX-SMT returned 'unknown' (timeout?)\n";
    is_time_limit_reached();
    try {
      smt_calls++;
      const unsigned timeout =
          static_cast<unsigned>(1000 * get_time_left(timer_category));
      params.set(":timeout", timeout);
      params.set("timeout", timeout);

      solver.set(params);
      res = solver.check();  // bat: if too long, solve a regular SMT instance
                             // (without any soft constraints)
    } catch (const z3::exception &except) {
      std::cout << "Exception: " << except << "\n";
      std::stringstream ss;
      ss << except;
      failure_cause = "SMT (z3) exception: " + ss.str();
      safe_exit(1);
    }
    if (debug) std::cout << "SMT result: " << res << "\n";
    if (res == z3::sat) {
      model = solver.get_model();
    }
  }
  return res;
}

bool Sampler::is_time_limit_reached(const std::string &category) {
  struct timespec now;
  clock_gettime(CLOCK_REALTIME, &now);
  double elapsed = duration(&timer_start_times[category], &now);
  if (elapsed >= max_times[category]) return true;
  if (should_exit) return true;
  return false;
}

// TODO: This function doesn't actually return bool...
bool Sampler::is_time_limit_reached() {
  if (should_exit) {
    std::cout << "Stopping: External timeout\n";
    failure_cause = "External timeout.";
    safe_exit(3);
  }
  if (is_time_limit_reached("total")) {
    std::cout << "Stopping: timeout\n";
    failure_cause = "Timeout.";
    safe_exit(0);
  }
  return false;
}

void Sampler::set_exit() volatile { should_exit = true; }

void Sampler::finish() {  // todo: remove exit and add where calling
  if (config.json) {
    write_json();
  }
  if ((is_timer_on.find("total") != is_timer_on.cend()) &&
      is_timer_on["total"]) {
    accumulate_time("total");
  }
  print_stats();
  if (!config.no_write)
  results_file.close();
}

void Sampler::write_json() {
  std::ofstream json_file;

  std::cout << "Writing to json file: " << json_filename << "\n";
  // todo: error handling? if input_filename does not exist we should not have
  // come this far... Also, if json_file exists- it runs it over
  json_file.open(json_filename);

  json_output["sat result"] = sat_result;
  json_output["result"] = result;
  json_output["failure cause"] = failure_cause;
  json_output["filename"] = input_filename;
  json_output["epochs"] = epochs;
  json_output["maxsmt calls"] = max_smt_calls;
  json_output["smt calls"] = smt_calls;
  json_output["total samples"] = (Json::UInt64)total_samples;
  json_output["valid samples"] = (Json::UInt64)valid_samples;
  json_output["unique valid samples"] = (Json::UInt64)unique_valid_samples;
  for (auto it = accumulated_times.cbegin(); it != accumulated_times.cend();
       ++it) {
    json_output["time stats"][it->first] = it->second;
  }
  for (auto it = max_times.cbegin(); it != max_times.cend(); ++it) {
    json_output["max time stats"][it->first] = it->second;
  }
  json_output["formula stats"]["num arrays"] = num_arrays;
  json_output["formula stats"]["num bvs"] = num_bv;
  json_output["formula stats"]["num bools"] = num_bools;
  json_output["formula stats"]["num uninterp funcs"] = num_uf;
  json_output["formula stats"]["num ints"] = num_ints;
  json_output["formula stats"]["num reals"] = num_reals;
  json_output["formula stats"]["formula AST depth"] = max_depth;
  json_output["options"]["use blocking"] = config.blocking;
  json_output["options"]["max samples"] = (Json::UInt64)config.max_samples;
  json_output["options"]["max epoch samples"] = (Json::UInt64)config.max_epoch_samples;
  json_output["options"]["debug"] = config.debug;
  json_output["options"]["one epoch"] = config.one_epoch;
  json_output["options"]["no samples output"] = config.no_write;

  Json::StreamWriterBuilder builder;
  builder["indentation"] = " ";
  std::unique_ptr<Json::StreamWriter> streamWriter(builder.newStreamWriter());
  streamWriter->write(json_output, &json_file);

  json_file.close();
}

void Sampler::print_stats() {
  std::cout << "---------SOLVING STATISTICS--------\n";
  for (auto it = accumulated_times.cbegin(); it != accumulated_times.cend();
       ++it) {
    std::cout << it->first << " time: " << it->second << '\n';
  }
  std::cout << "Epochs: " << epochs << '\n';
  std::cout << "MAX-SMT calls: " << max_smt_calls << '\n';
  std::cout << "SMT calls: " << smt_calls << '\n';
  std::cout << "Assignments considered (with repetitions): " << total_samples
            << '\n';
  std::cout << "Models (with repetitions): " << valid_samples << '\n';
  std::cout << "Unique models (# samples in file): " << unique_valid_samples
            << '\n';
  std::cout << "-----------------------------------" << std::endl;
}

z3::model Sampler::start_epoch() {
  is_time_limit_reached();

  if (debug)
    std::cout << "Sampler: Starting an epoch (" << epochs << ")" << std::endl;

  if (!config.blocking)
    opt.push();  // because formula is constant, but other hard/soft constraints
                 // change between epochs
  if (config.blocking) {
    add_blocking_soft_constraints();
  } else {
    choose_random_assignment();
  }
  z3::check_result res =
      solve("epoch", !config.blocking && !config.avoid_maxsmt);

  if (config.blocking && res == z3::unsat) {
    /* we blocked everything, lets start over */
    solver.pop();
    solver.push();
    res = solve("epoch", false);
  }

  assert(res != z3::unsat);
  if (!config.blocking) opt.pop();

  epochs++;
  total_samples++;

  if (res == z3::sat) save_and_output_sample_if_unique(model_to_string(model));

  return model;
}

void Sampler::choose_random_assignment() {
  for (z3::func_decl &v : variables) {
    if (v.arity() > 0 || v.range().is_array()) continue;
    switch (v.range().sort_kind()) {
      case Z3_BV_SORT:  // random assignment to bv
      {
        if (random_soft_bit) {
          for (size_t i = 0; i < v.range().bv_size(); ++i) {
            if (rand() % 2)
              assert_soft(v().extract(i, i) == c.bv_val(0, 1));
            else
              assert_soft(v().extract(i, i) != c.bv_val(0, 1));
          }
        } else {
          std::string n;
          char num[10];
          int i = v.range().bv_size();
          if (i % 4) {
            snprintf(num, 10, "%x", rand() & ((1 << (i % 4)) - 1));
            n += num;
            i -= (i % 4);
          }
          while (i) {
            snprintf(num, 10, "%x", rand() & 15);
            n += num;
            i -= 4;
          }
          Z3_ast ast = parse_bv(n.c_str(), v.range(), c);
          z3::expr exp(c, ast);
          assert_soft(v() == exp);
        }
        break;  // from switch, bv case
      }
      case Z3_BOOL_SORT:  // random assignment to bool var
        if (rand() % 2)
          assert_soft(v());
        else
          assert_soft(!v());
        break;           // from switch, bool case
      case Z3_INT_SORT:  // random assignment to bool var
      {
        const int random = rand();
        if (rand() % 2)
          assert_soft(v() == c.int_val(random));
        else
          assert_soft(v() == c.int_val(-random));
      } break;  // from switch, int case
      default:
        // TODO add real
        std::cout << "Invalid sort\n";
        failure_cause = "Invalid sort.";
        safe_exit(1);
    }
  }  // end for: random assignment chosen
}

void Sampler::add_blocking_soft_constraints() {
  if (debug) std::cout << "Using blocking :)\n";
  for (unsigned int i = 0; i < model.num_consts(); ++i) {
    const auto &decl = model.get_const_decl(i);
    assert_soft(decl() != model.get_const_interp(decl));
  }
#if 0  // TODO: Revisit if we have non-const functions
    for (unsigned int i = 0; i < model.num_funcs(); ++i) {
        const auto& decl = model.get_func_decl(i);
        assert_soft(decl() != model.get_func_interp(decl));
    }
#endif
}

void Sampler::do_epoch(__attribute__((unused)) const z3::model &m) {
  std::cout << "Sampler: Epoch: keeping only original model" << std::endl;
}

void Sampler::compute_and_print_formula_stats() {
  // TODO save formula theory
  _compute_formula_stats_aux(original_formula);
  //	std::cout << "Nodes " << sup.size() << '\n';
  //	std::cout << "Internal nodes " << sub.size() << '\n';
  std::cout << "-------------FORMULA STATISTICS-------------" << '\n';
  std::cout << "Arrays " << num_arrays << '\n';
  std::cout << "Bit-vectors " << num_bv << '\n';
  std::cout << "Bools " << num_bools << '\n';
  std::cout << "Bits " << num_bits << '\n';
  std::cout << "Uninterpreted functions " << num_uf << '\n';
  std::cout << "Ints " << num_ints << '\n';
  std::cout << "Reals " << num_reals << '\n';
  std::cout << "Formula tree depth " << max_depth << '\n';
  std::cout << "--------------------------------------------" << '\n';
}

void Sampler::_compute_formula_stats_aux(z3::expr e, int depth) {
  if (sup.find(e) != sup.end()) return;
  assert(e.is_app());
  z3::func_decl fd = e.decl();
  if (e.is_const()) {
    std::string name = fd.name().str();
    if (var_names.find(name) == var_names.end()) {
      var_names.insert(name);
      variables.push_back(fd);
      variable_names.push_back(name);
      if (fd.range().is_array()) {
        ++num_arrays;
      } else if (fd.is_const()) {
        switch (fd.range().sort_kind()) {
          case Z3_BV_SORT:
            ++num_bv;
            num_bits += fd.range().bv_size();
            break;
          case Z3_BOOL_SORT:
            ++num_bools;
            ++num_bits;
            break;
          case Z3_INT_SORT:
            ++num_ints;
            break;
          case Z3_REAL_SORT:
            ++num_reals;
            break;
          default:
            std::cout << "Invalid sort\n";
            failure_cause = "Invalid sort.";
            safe_exit(1);
        }
      }
    }
  } else if (fd.decl_kind() == Z3_OP_UNINTERPRETED) {
    std::string name = fd.name().str();
    if (var_names.find(name) == var_names.end()) {
      var_names.insert(name);
      // std::cout << "declaration: " << fd << '\n';
      variables.push_back(fd);
      ++num_uf;
    }
  }
  //  if (e.is_bool() || e.is_bv()) { // todo figure out if we need sub for the
  //  smtsampler implementation
  //	  sub.insert(e);
  //  }
  sup.insert(e);
  if (depth > max_depth) {
    max_depth = depth;
  }
  for (size_t i = 0; i < e.num_args(); ++i) {
    _compute_formula_stats_aux(e.arg(i), depth + 1);
  }
}

void Sampler::assert_soft(z3::expr const &e) { opt.add(e, 1); }

bool Sampler::save_and_output_sample_if_unique(const std::string &sample) {
  valid_samples++;
  set_timer_on("output");
  const auto res = samples.insert(sample);
  if (res.second) {
    unique_valid_samples++;
    if (!config.no_write)
      results_file << unique_valid_samples << ": " << sample << '\n';
  }
  accumulate_time("output");
  if (unique_valid_samples >= config.max_samples) {
    failure_cause = "Reached max samples.";
    safe_exit(0);
  }
  return res.second;
}

std::string Sampler::model_to_string(const z3::model &m) {
  std::string s;
  s.reserve(10 + num_arrays * 25 + num_ints * 10);
  for (const auto &v : variables) {
    if (v.range().is_array()) {  // array case
      s += v.name().str() + ':';
      if (!m.has_interp(v)) {
        //          failure_cause = "variable not in model";
        //          safe_exit(1);
        continue;
      }
      z3::expr e = m.get_const_interp(v);
      assert(e);
      Z3_func_decl as_array = Z3_get_as_array_func_decl(c, e);
      if (as_array) {
        z3::func_interp f = m.get_func_interp(to_func_decl(c, as_array));
        s += "[";
        s += std::to_string(f.num_entries());
        s += ",";
        s += f.else_value().to_string();
        s += ',';
        for (size_t j = 0; j < f.num_entries(); ++j) {
          s += f.entry(j).arg(0).to_string() + "->";
          s += f.entry(j).value().to_string() + ',';
        }
        s += "];";
      } else {
        std::vector<std::string> args;
        std::vector<std::string> values;
        while (e.decl().name().str() == "store") {
          std::string arg = e.arg(1).to_string();
          if (std::find(args.begin(), args.end(), arg) != args.end()) {
            e = e.arg(0);
            continue;
          }
          args.push_back(arg);
          values.push_back(e.arg(2).to_string());
          e = e.arg(0);
        }
        s += "[";
        s += std::to_string(args.size());
        s += ',';
        s += e.arg(0).to_string();
        s += ',';
        for (int j = args.size() - 1; j >= 0; --j) {
          s += args[j];
          s += "->";
          s += values[j];
          s += ',';
        }
        s += "];";
      }

    } else if (v.is_const()) {  // BV, Int case
      s += v.name().str();
      s += ':';
      z3::expr b = m.get_const_interp(v);
      Z3_ast ast = b;
      switch (v.range().sort_kind()) {
        case Z3_BV_SORT:
          if (!ast) {
            s += bv_string(c.bv_val(0, v.range().bv_size()), c);
          } else {
            s += bv_string(b, c);
          }
          break;
        case Z3_BOOL_SORT:
          if (!ast) {
            s += std::to_string(false);
          } else {
            s += std::to_string(b.bool_value() == Z3_L_TRUE);
          }
          break;
        case Z3_INT_SORT:
          if (!ast) {
            s += std::to_string(0);
          } else {
            std::string number;
            b.is_numeral(number);
            s += number;
          }
          break;
        default:
          std::cout << "Invalid sort\n";
          failure_cause = "Invalid sort.";
          safe_exit(1);
      }
      s += ';';
    } else {  // Uninterpreted function
      s += v.name().str() + ':';
      z3::func_interp f = m.get_func_interp(v);
      std::string num = "(";
      num += std::to_string(f.num_entries());
      s += num;
      s += ';';
      std::string def = std::to_string(f.else_value());
      s += def;
      s += ';';
      for (size_t j = 0; j < f.num_entries(); ++j) {
        for (size_t k = 0; k < f.entry(j).num_args(); ++k) {
          std::string arg = std::to_string(f.entry(j).arg(k));
          s += arg + ':';
        }
        std::string val = std::to_string(f.entry(j).value());
        s += val + ',';
      }
      s += ");";
    }
  }
  return s;
}

void Sampler::set_timer_on(const std::string &category) {
  if (is_timer_on.find(category) != is_timer_on.end() &&
      is_timer_on[category]) {  // category was inserted to map and its value
                                // was set to true
    std::cerr << "WARNING: starting timer twice for category " << category
              << std::endl;
  }
  struct timespec now;
  clock_gettime(CLOCK_REALTIME, &now);
  timer_start_times[category] = now;
  is_timer_on[category] = true;
}

void Sampler::accumulate_time(const std::string &category) {
  if (is_timer_on.find(category) == is_timer_on.end() ||
      is_timer_on[category] == false) {  // timer never went on
    std::cerr << "ERROR: cannot stop timer for category: " << category
              << ". Timer was never started." << std::endl;
    failure_cause = "Timer stopped before started.";
    safe_exit(1);  // TODO add exception handling
  }

  assert(timer_start_times.find(category) != timer_start_times.end());
  struct timespec now;
  clock_gettime(CLOCK_REALTIME, &now);
  if (accumulated_times.find(category) == accumulated_times.end()) {
    accumulated_times[category] = 0.0;
  }
  accumulated_times[category] += duration(&timer_start_times[category], &now);

  is_timer_on[category] = false;
}

void Sampler::set_timer_max(const std::string &category, double limit) {
  max_times[category] = limit;
}

void Sampler::safe_exit(int exitcode) {
  if (exitcode) {
    result = "failure";
  } else {
    result = "success";
  }
  finish();
  exit(exitcode);
}

void Sampler::set_model(const z3::model &new_model) { model = new_model; }

void Sampler::set_epochs(int _epochs) { epochs = _epochs; }
