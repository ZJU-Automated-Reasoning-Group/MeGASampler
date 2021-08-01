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
	printf("SMTSAMPLER: do epoch\n");

    std::unordered_set<std::string> mutations;
    std::string m_string = model_string(m, ind);

//    opt.push();
//    solver.push();

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
	  if (v.range().is_array()) {
		assert(m_string.c_str()[pos] == '[');
		++pos;
		int num = atoi(m_string.c_str() + pos);
		pos = m_string.find('\0', pos) + 1;

		z3::expr def = value(m_string.c_str() + pos, v.range().array_range());
		pos = m_string.find('\0', pos) + 1;

		for (int j = 0; j < num; ++j) {
		  z3::expr arg =
			  value(m_string.c_str() + pos, v.range().array_domain());
		  pos = m_string.find('\0', pos) + 1;
		  z3::expr val = value(m_string.c_str() + pos, v.range().array_range());
		  pos = m_string.find('\0', pos) + 1;

		  add_constraints(z3::select(v(), arg), val, -1);
		}
		assert(m_string.c_str()[pos] == ']');
		++pos;
	  } else if (v.is_const()) {
		z3::expr a = value(m_string.c_str() + pos, v.range());
		pos = m_string.find('\0', pos) + 1;
		add_constraints(v(), a, count);
	  } else {
		assert(m_string.c_str()[pos] == '(');
		++pos;
		int num = atoi(m_string.c_str() + pos);
		pos = m_string.find('\0', pos) + 1;

		z3::expr def = value(m_string.c_str() + pos, v.range());
		pos = m_string.find('\0', pos) + 1;

		for (int j = 0; j < num; ++j) {
		  z3::expr_vector args(c);
		  for (int k = 0; k < v.arity(); ++k) {
			z3::expr arg = value(m_string.c_str() + pos, v.domain(k));
			pos = m_string.find('\0', pos) + 1;
			args.push_back(arg);
		  }
		  z3::expr val = value(m_string.c_str() + pos, v.range());
		  pos = m_string.find('\0', pos) + 1;

		  add_constraints(v(args), val, -1);
		}
		assert(m_string.c_str()[pos] == ')');
		++pos;
	  }
	}
}

std::string SMTSampler::model_string(z3::model m, std::vector<z3::func_decl> ind) {
  std::string s;
  for (z3::func_decl &v : ind) {
    if (v.range().is_array()) {
      z3::expr e = m.get_const_interp(v);
      Z3_func_decl as_array = Z3_get_as_array_func_decl(c, e);
      if (as_array) {
        z3::func_interp f = m.get_func_interp(to_func_decl(c, as_array));
        std::string num = "[";
        num += std::to_string(f.num_entries());
        s += num + '\0';
        std::string def = bv_string(f.else_value(), c);
        s += def + '\0';
        for (int j = 0; j < f.num_entries(); ++j) {
          std::string arg = bv_string(f.entry(j).arg(0), c);
          std::string val = bv_string(f.entry(j).value(), c);
          s += arg + '\0';
          s += val + '\0';
        }
        s += "]";
      } else {
        std::vector<std::string> args;
        std::vector<std::string> values;
        while (e.decl().name().str() == "store") {
          std::string arg = bv_string(e.arg(1), c);
          if (std::find(args.begin(), args.end(), arg) != args.end())
            continue;
          args.push_back(arg);
          values.push_back(bv_string(e.arg(2), c));
          e = e.arg(0);
        }
        std::string num = "[";
        num += std::to_string(args.size());
        s += num + '\0';
        std::string def = bv_string(e.arg(0), c);
        s += def + '\0';
        for (int j = args.size() - 1; j >= 0; --j) {
          std::string arg = args[j];
          std::string val = values[j];
          s += arg + '\0';
          s += val + '\0';
        }
        s += "]";
      }
    } else if (v.is_const()) {
      z3::expr b = m.get_const_interp(v);
      Z3_ast ast = b;
      switch (v.range().sort_kind()) {
      case Z3_BV_SORT: {
        if (!ast) {
          s += bv_string(c.bv_val(0, v.range().bv_size()), c) + '\0';
        } else {
          s += bv_string(b, c) + '\0';
        }
        break;
      }
      case Z3_BOOL_SORT: {
        if (!ast) {
          s += std::to_string(false) + '\0';
        } else {
          s += std::to_string(b.bool_value() == Z3_L_TRUE) + '\0';
        }
        break;
      }
      default:
        std::cout << "Invalid sort\n";
        exit(1);
      }
    } else {
      z3::func_interp f = m.get_func_interp(v);
      std::string num = "(";
      num += std::to_string(f.num_entries());
      s += num + '\0';
      std::string def = bv_string(f.else_value(), c);
      s += def + '\0';
      for (int j = 0; j < f.num_entries(); ++j) {
        for (int k = 0; k < f.entry(j).num_args(); ++k) {
          std::string arg = bv_string(f.entry(j).arg(k), c);
          s += arg + '\0';
        }
        std::string val = bv_string(f.entry(j).value(), c);
        s += val + '\0';
      }
      s += ")";
    }
  }
  return s;
}

z3::expr SMTSampler::value(char const *n, z3::sort s) {
  switch (s.sort_kind()) {
  case Z3_BV_SORT: {
    Z3_ast ast = parse_bv(n, s, c);
    z3::expr exp(c, ast);
    return exp;
  }
  case Z3_BOOL_SORT:
    return c.bool_val(atoi(n) == 1);
  default:
    std::cout << "Invalid sort\n";
    exit(1);
  }
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
