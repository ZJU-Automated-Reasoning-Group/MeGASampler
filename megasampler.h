#ifndef MEGASAMPLER_H_
#define MEGASAMPLER_H_

#include "sampler.h"
#include "strengthen.capnp.h"

class MEGASampler : public Sampler {
  z3::expr simpl_formula;

 public:
  MEGASampler(std::string input, std::string output_dir, int max_samples,
              double max_time, int max_epoch_samples, double max_epoch_time,
              int strategy, bool json, bool blocking);
  /*
   * Override from sampler
   */
  void do_epoch(const z3::model& model);
  void finish();
  virtual void add_blocking_soft_constraints() { /* do nothing */ }


 private:
  void sample_intervals_in_rounds(
      const capnp::List<StrengthenResult::VarInterval>::Reader& intervalmap);
  std::string get_random_sample_from_intervals(
      const capnp::List<StrengthenResult::VarInterval>::Reader& intervalmap);
  void add_soft_constraint_from_intervals(
      const capnp::List<StrengthenResult::VarInterval>::Reader& intervalmap);

};

#endif /* MEGASAMPLER_H_ */
