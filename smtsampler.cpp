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

void SMTSampler::do_epoch(const z3::model &m) {
	std::cout << "SMTSAMPLER: do epoch\n";

    std::unordered_set<std::string> mutations;
    std::string m_string = model_string(m, ind);

    opt.push();
    solver.push();

    constraints.clear();
    soft_constraints.clear();
    cons_to_ind.clear();
    all_ind_count = 0;

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
//        add_constraints(v(), a, count);
	}
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


void SMTSampler::add_constraints(z3::expr exp, z3::expr val, int count) {
  switch (val.get_sort().sort_kind()) {
  case Z3_BV_SORT: {
    std::vector<z3::expr> soft;
    for (int i = 0; i < val.get_sort().bv_size(); ++i) {
      all_ind_count += (count >= 0);
      cons_to_ind.emplace_back(count, i);

      z3::expr r = val.extract(i, i);
      r = r.simplify();
      constraints.push_back(exp.extract(i, i) == r);
      // soft.push_back(exp.extract(i, i) == r);
      if (strategy == STRAT_SMTBIT)
        assert_soft(exp.extract(i, i) == r);
    }
    for (int i = 0; i < val.get_sort().bv_size(); ++i) {
      soft_constraints.push_back(soft);
    }
    if (strategy == STRAT_SMTBV)
      assert_soft(exp == val);
    break;
  }
  case Z3_BOOL_SORT: {
    all_ind_count += (count >= 0);
    cons_to_ind.emplace_back(count, 0);
    constraints.push_back(exp == val);
    std::vector<z3::expr> soft;
    soft_constraints.push_back(soft);
    assert_soft(exp == val);
    break;
  }
  default:
    std::cout << "Invalid sort\n";
    exit(1);
  }
}
