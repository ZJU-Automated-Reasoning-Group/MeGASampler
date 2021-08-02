#include "smtsampler.h"

SMTSampler::SMTSampler(std::string input, int max_samples, double max_time,
                         int max_epoch_samples, double max_epoch_time,
                         int strategy)
    : Sampler(input, max_samples, max_time, max_epoch_samples, max_epoch_time,
              strategy), strategy(strategy) {
    initialize_solvers();
//  if (!convert) {
    ind = variables;
//  }
    std::cout << "starting SMTSampler" << std::endl;
}

void SMTSampler::calculate_constraints(const std::string &m_string) {
	//todo uncomment? is this necessary?
	//	if (flip_internal) {
	//		for (z3::expr &v : internal) {
	//			z3::expr b = m.eval(v, true);
	//			cons_to_ind.emplace_back(-1, -1);
	//			constraints.push_back(v == b);
	//			std::vector<z3::expr> soft;
	//			soft_constraints.push_back(soft);
	//		}
	//	}
	size_t pos = 0;
	for (int count = 0; count < ind.size(); ++count) {
		z3::func_decl &v = ind[count];
		assert(v.is_const() and v.range().sort_kind() == Z3_INT_SORT);
		z3::expr a = value(m_string.c_str() + pos, v.range());
		pos = m_string.find(';', pos) + 1;
		add_constraints(v(), a, count);
	}
	std::cout << "Collected constraints: ";
	for (auto c : constraints) {
		std::cout << c << " ";
	}
	std::cout << "\n";
}

void SMTSampler::find_neighboring_solutions(
		std::unordered_set<std::string> mutations) {
	// STEP 2: mutate constraints to get Sigma_1 (solutions of distance 1)
	struct timespec etime;
	clock_gettime(CLOCK_REALTIME, &etime);
	double start_epoch = duration(&start_time, &etime);
	int calls = 0;
	int progress = 0;
	for (int count = 0; count < constraints.size(); ++count) {
		//todo uncomment? is this necessary?
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
		// probably redundent: soft seems to always be empty
		//		for (z3::expr &soft : soft_constraints[count]) {
		//			assert_soft(soft);
		//		}
		struct timespec end;
		clock_gettime(CLOCK_REALTIME, &end);
		double elapsed = duration(&start_time, &end);
		double cost = calls ? (elapsed - start_epoch) / calls : 0.0;
		cost *= constraints.size() - count;
		if (max_time / 3.0 + start_epoch > max_time
				&& elapsed + cost > max_time) {
			std::cout << "Stopping: slow\n";
			finish();
		}
		z3::check_result result = z3::unknown;
		if (cost * rand() <= (max_time / 3.0 + start_epoch - elapsed) * RAND_MAX) {
			result = solve();
			++calls;
		}
		if (result == z3::sat) {
			std::string new_string = model_string(model, ind);
			if (mutations.find(new_string) == mutations.end()) {
				mutations.insert(new_string);
				std::string sample_to_file = model_to_string(model);
//				std::cout << "mutation: " << sample_to_file << "\n";
				save_and_output_sample_if_unique(sample_to_file); //todo: check format
				flips += 1;
			} else {
				std::cout << "repeated\n";
			}
		} else if (result == z3::unsat) {
			std::cout << "unsat\n";
			if (cons_to_ind[count].first >= 0) {
				unsat_ind[cons_to_ind[count].first].insert(
						cons_to_ind[count].second);
				++unsat_ind_count;
			}
		}

		opt.pop();
		solver.pop();
		// print === as a progress bar (80 '=' to mark 100% of constraints flipped)
		double new_progress = 80.0 * (double) ((count + 1))
				/ (double) (constraints.size());
		while (progress < new_progress) {
			++progress;
			std::cout << '=' << std::flush;
		}
	}
	std::cout << '\n';
}

void SMTSampler::do_epoch(const z3::model &m) {
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
    // STEP 2: mutate constraints to get Sigma_1 (solutions of distance 1)
	find_neighboring_solutions(mutations);
}

std::string SMTSampler::model_string(z3::model m, std::vector<z3::func_decl> ind) {
  std::string s;
  for (z3::func_decl &v : ind) {
		assert(v.is_const() and v.range().sort_kind() == Z3_INT_SORT);
		z3::expr b = m.get_const_interp(v);
		Z3_ast ast = b;
		assert(ast); // model should have an interpretation for all variables
		std::stringstream ss;
		ss << b;
		s += ss.str() + ';';
  }
  return s;
}

z3::expr SMTSampler::value(char const *n, z3::sort s) {
	assert(s.sort_kind() == Z3_INT_SORT && n);
	int value = atoi(n);
	if (n[0] == '('){ // if n is negative we need to remove the brackets
		assert(n[1] == '-' && n[2] == ' ');
		value = -atoi(n + 3);
	}
	return c.int_val(value);
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

