#ifndef MEGASAMPLER_H_
#define MEGASAMPLER_H_

#include "sampler.h"
#include "strengthen.capnp.h"

class MEGASampler : public Sampler {
 public:
  typedef capnp::List<StrengthenResult::VarInterval>::Reader capnpIntervalMap;
  typedef ::StrengthenResult::VarInterval::Reader capnpVarInterval;
  typedef ::StrengthenResult::VarInterval::Interval::Reader capnpInterval;

 private:
  z3::expr simpl_formula;
  int aux_array_index = 0;
  std::map<std::string,std::pair<std::string,std::string>> aux_array_map;
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

 public:
  MEGASampler(std::string input, std::string output_dir, int max_samples,
              double max_time, int max_epoch_samples, double max_epoch_time,
              int strategy, bool json, bool blocking);
  /*
   * Override from sampler
   */
  z3::model start_epoch();
  void do_epoch(const z3::model& model);
  void finish();
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
  std::string get_random_sample_from_int_intervals(
      const capnpIntervalMap& intervalmap);
  std::string get_random_sample_from_array_intervals(
      const capnpIntervalMap& intervalmap,
      const std::vector<arrayAccessData>& indexvec);
  void add_soft_constraint_from_intervals(
      const capnpIntervalMap& intervalmap,
      const std::vector<arrayAccessData>& index_vec);
  z3::expr deserialise_expr(const std::string& str);
};

#endif /* MEGASAMPLER_H_ */
