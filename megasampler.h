#ifndef MEGASAMPLER_H_
#define MEGASAMPLER_H_

#include "sampler.h"

class MEGASampler : public Sampler {

  z3::expr simpl_formula;

public:
  MEGASampler(std::string input, int max_samples, double max_time,
              int max_epoch_samples, double max_epoch_time, int strategy, bool json);

  /*
   * Override from sampler
   */
  void do_epoch(const z3::model &model);
  void finish();

private:
  void sample_intervals_in_rounds(const auto& intervalmap);
  std::string get_random_sample_from_intervals(const auto& intervalmap);
};

#endif /* MEGASAMPLER_H_ */
