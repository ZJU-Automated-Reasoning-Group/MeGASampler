#ifndef MEGASAMPLER_H_
#define MEGASAMPLER_H_

#include <list>
#include <set>

#include "sampler.h"
#include "strengthen.capnp.h"
#include "strengthener.h"

class MEGASampler : public Sampler {
 public:
  typedef capnp::List<StrengthenResult::VarInterval>::Reader capnpIntervalMap;
  typedef ::StrengthenResult::VarInterval::Reader capnpVarInterval;
  typedef ::StrengthenResult::VarInterval::Interval::Reader capnpInterval;

 private:
  z3::expr simpl_formula;
  z3::expr implicant;

  // data structure for parsing intervals over select terms and sampling them
  struct arrayAccessData {
    capnpVarInterval entryInCapnpMap;
    z3::expr indexExpr;
    int numSelecetsInIndex;
    arrayAccessData(const capnpVarInterval e, z3::expr i, int n)
        : entryInCapnpMap(e), indexExpr(i), numSelecetsInIndex(n) {}
    std::string toString() {
      return "index " + indexExpr.to_string() + " in array " +
             entryInCapnpMap.getVariable().cStr() + " has " +
             std::to_string(numSelecetsInIndex) + " selects.";
    }
    bool operator<(const arrayAccessData& d) const {
      return numSelecetsInIndex < d.numSelecetsInIndex;
    }
  };

  // data structures for removing array equalities
  struct storeEqIndexValue {
      int64_t value;
      int serial_number_in_array;
      z3::expr index_expr;
      z3::expr value_expr;
      bool in_a; // index is either in 'a' array (base array of arg(0)) or 'b' array of a store_eq.
      storeEqIndexValue(z3::context& c): index_expr(c), value_expr(c) {}
      std::string to_string() {
        return "storeEqIndexValue for index_expr: " + index_expr.to_string() +
               " and value expr: " + value_expr.to_string() +
               " from array " + (in_a ? "a" : "b") +
               " has value: " + std::to_string(value);
      }
      bool operator<(const storeEqIndexValue& seq) const {
        return value < seq.value ||
               (value == seq.value && in_a == seq.in_a && serial_number_in_array < seq.serial_number_in_array);
      }
  };
  struct arrayEqualityEdge {
    z3::expr store_e;
    z3::expr_vector a_indices;
    z3::expr_vector a_values;
    z3::expr_vector b_indices;
    z3::expr_vector b_values;
    z3::expr a;
    z3::expr b;
    bool in_implicant = false;
    std::vector<storeEqIndexValue> index_values;
    arrayEqualityEdge(z3::context& c): store_e(c), a_indices(c), a_values(c), b_indices(c), b_values(c), a(c), b(c) {}
    std::string toString() {
      return std::string("arrayEqualityEdge (") + (in_implicant ? "turned on" : "turned off") + ") for expression: " + store_e.to_string() + ":\n" +
      a.to_string() + ": indices:" + a_indices.to_string() + "; values:" + a_values.to_string() +
      "\nand\n" +
      b.to_string() + ": indices:" + b_indices.to_string() + "; values:" + b_values.to_string();
    }
  };
  typedef std::map<std::string, std::list<arrayEqualityEdge>> arrayEqualityGraph_t;
  arrayEqualityGraph_t arrayEqualityGraph;

 public:
  MEGASampler(std::string input, std::string output_dir, int max_samples,
              double max_time, int max_epoch_samples, double max_epoch_time,
              int strategy, bool json, bool blocking);
  /*
   * Override from sampler
   */
  void do_epoch(const z3::model& model);
  void finish();
  void initialize_solvers(); // for MEGA, solve simpl_formula, not original_formula
  virtual void add_blocking_soft_constraints() { /* do nothing */
  }

 private:
    /*
     * Changes the formula being solved by getting rid of array equalities over different arrays.
     * An equality store(... store(a,i1,t1)..in,tn)=store(...store(b,j1,s1)...jm,sm)
     * is replaced with same equality over auxiliary array variable named aux_a_<aux_array_index>.
     * In addition, a is replaced anywhere else in the formula with store(... store(aux_a,i1,select(a,i1))..in,select(a,in))
     * and similarily for b.
     * The entry aux_a->(a,b) is inserted to aux_array_map.
     */
  void eliminate_eq_of_different_arrays();
  void sample_intervals_in_rounds(
      const capnpIntervalMap& intervalmap,
      const std::vector<arrayAccessData>& index_vec);
  void sample_intervals_in_rounds(
          const IntervalMap& intervalmap,
          const std::vector<arrayAccessData>& index_vec);
  std::string get_random_sample_from_int_intervals(
      const capnpIntervalMap& intervalmap);
  std::string get_random_sample_from_int_intervals(
      const IntervalMap& intervalmap);
  std::string get_random_sample_from_array_intervals(
      const capnpIntervalMap& intervalmap,
      const std::vector<arrayAccessData>& indexvec);
  std::string get_random_sample_from_array_intervals(
      const IntervalMap& intervalmap,
      const std::vector<arrayAccessData>& indexvec);
  void add_soft_constraint_from_intervals(
      const capnpIntervalMap& intervalmap,
      const std::vector<arrayAccessData>& index_vec);
  z3::expr deserialise_expr(const std::string& str);
  /*
   * simplifies original_formula and saves the result in simpl_fomrula
   */
  void simplify_formula();
  /*
   * return formula.substitute(z3!name,mega!z3!name) for all z3!names
   */
  z3::expr rename_z3_names(z3::expr& formula);
  void print_array_equality_graph();
  void register_array_eq(z3::expr& f);
  void remove_array_equalities(std::list<z3::expr>& conjuncts);
  void add_equalities_from_select_terms(std::list<z3::expr>& conjuncts);
  void add_opposite_array_constraint(const MEGASampler::storeEqIndexValue& curr_ival,
                                    const MEGASampler::arrayEqualityEdge& store_eq, std::list<z3::expr>& conjuncts);
  void add_value_clash_constraint(const MEGASampler::storeEqIndexValue& curr_ival,
                                    const MEGASampler::storeEqIndexValue& next_ival, std::list<z3::expr>& conjuncts);
  void build_index_value_vector(arrayEqualityEdge& store_eq);
  void remove_duplicates_in_index_values(arrayEqualityEdge& store_eq);
  void add_index_relationship_constraints(const arrayEqualityEdge& store_eq, std::list<z3::expr>& conjuncts);
  void add_array_value_constraints(const arrayEqualityEdge& store_eq, std::list<z3::expr>& conjuncts);
  void array_equality_graph_BFS(const z3::expr& array, const z3::expr& index, int64_t value, std::list<z3::expr>& new_conjucts);
};

#endif /* MEGASAMPLER_H_ */
