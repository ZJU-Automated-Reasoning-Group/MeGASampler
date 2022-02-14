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

  struct arrayAccessData {
      capnpVarInterval entryInCapnpMap;
      z3::expr indexExpr;
      int numSelecetsInIndex;
      arrayAccessData(const capnpVarInterval e, z3::expr i, int n): entryInCapnpMap(e), indexExpr(i), numSelecetsInIndex(n){}
      std::string toString() {
          return "index " + indexExpr.to_string() + " in array " + entryInCapnpMap.getVariable().cStr() + " has " + std::to_string(numSelecetsInIndex) + " selects.";
      }
      bool operator < (const arrayAccessData& d) const{
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
  void do_epoch(const z3::model& model);
  void finish();
  virtual void add_blocking_soft_constraints() { /* do nothing */
  }

 private:
  void sample_intervals_in_rounds(
      const capnpIntervalMap& intervalmap, const std::vector<arrayAccessData>& index_vec);
  std::string get_random_sample_from_int_intervals(
      const capnpIntervalMap& intervalmap);
  std::string get_random_sample_from_array_intervals(
      const capnpIntervalMap& intervalmap, const std::vector<arrayAccessData>& indexvec);
  void add_soft_constraint_from_intervals(
      const capnpIntervalMap& intervalmap);
  z3::expr deserialise_expr(const std::string & str);
};

#endif /* MEGASAMPLER_H_ */
