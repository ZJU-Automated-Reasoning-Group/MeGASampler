// rainoftime

#ifndef Z3PLUS_H_
#define Z3PLUS_H_
#include <vector>
#include <set>
#include <future>
#include <map>
#include <iostream>
#include <memory>
#include <set>
#include <vector>
#include <algorithm>
#include "z3++.h"
#include "z3.h"

using namespace z3;
using namespace std;

bool get_expr_vars(expr& exp, expr_vector& vars) {
    // TODO: test the efficiency of this function
    try {
        auto& ctx = exp.ctx();
        auto compare_func = [](const z3::expr& a, const z3::expr& b) {
            Z3_symbol sym_a = a.decl().name();
            Z3_symbol sym_b = b.decl().name();
            return sym_a < sym_b;
        };
        std::set<z3::expr, decltype(compare_func)> syms(compare_func);
        std::function<void(const z3::expr&)> recur = [&recur, &syms, &ctx](
                const z3::expr& e) {
            assert(Z3_is_app(ctx, e));
            auto app = Z3_to_app(ctx, e);
            unsigned n_args = Z3_get_app_num_args(ctx, app);

            auto fdecl = Z3_get_app_decl(ctx, app);
            if (n_args == 0 && Z3_get_decl_kind(ctx, fdecl) == Z3_OP_UNINTERPRETED)
                syms.insert(e);

            for (unsigned i = 0; i < n_args; ++i) {
                z3::expr arg(ctx, Z3_get_app_arg(ctx, app, i));
                recur(arg);
            }
        };
        recur(exp);
        // if the return type is std::vector<z3::expr>
        //return std::vector<z3::expr>(syms.begin(), syms.end());;
        for (auto& i : syms) {
            vars.push_back(i);
        }
    } catch (z3::exception & ex) {
        std::cout << ex.msg() << std::endl;
        return false;
    }
    return true;
}
// note that we assume vars_a and vars_b consist of purely variables.
expr_vector get_vars_difference(expr_vector& vars_a, expr_vector& vars_b) {
    expr_vector ret(vars_a.ctx());
    try {
        for (unsigned i = 0; i < vars_a.size(); i++) {
            bool is_in_diff = true;
            Z3_symbol sym_i = vars_a[i].decl().name();
            for (unsigned j = 0; j < vars_b.size(); j++) {
                if (sym_i == vars_b[j].decl().name()) { is_in_diff = false; }
            }
            if (is_in_diff) { ret.push_back(vars_a[i]); }
        }
    } catch (z3::exception & ex) {
        std::cout << ex.msg() << std::endl;
        return ret;
    }
    return ret;
}


void get_abstract_interval_as_expr(expr& pre_cond, expr& query, expr_vector& res, int timeout) {
    context &Ctx = pre_cond.ctx();

    params Param(Ctx);
    Param.set("priority", Ctx.str_symbol("box"));
    //set_param("smt.timeout", (int)timeout);
    Param.set("timeout", (unsigned)timeout);

    optimize LowerFinder(Ctx);
    LowerFinder.set(Param);
    LowerFinder.add(pre_cond);
    optimize::handle LowerGoal = LowerFinder.minimize(query);
    try {
        if (LowerFinder.check() == z3::sat) {
            expr lower = LowerFinder.upper(LowerGoal);
            res.push_back(lower);
        }
    } catch(z3::exception &Ex) {
        res.push_back(Ctx.bool_val(false));
    }

    optimize UpperFinder(Ctx);
    UpperFinder.set(Param);
    UpperFinder.add(pre_cond);
    optimize::handle UpperGoal = UpperFinder.maximize(query);
    try {
        if (UpperFinder.check() == z3::sat) {
            expr upper = UpperFinder.lower(UpperGoal);
            res.push_back(upper);
        }
    } catch(z3::exception &Ex) {
        res.push_back(Ctx.bool_val(false));
    }
}





#endif /* Z3PLUS_H_ */
