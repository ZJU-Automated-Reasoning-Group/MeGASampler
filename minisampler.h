#ifndef MINISAMPLER_H_
#define MINISAMPLER_H_
#include "sampler.h"

class MiniSampler : public Sampler {
 public:
  using Sampler::Sampler;
  void do_epoch(__attribute__((unused)) const z3::model &m) {
    /* do nothing, all the work was done in Sampler::start_epoch */
  }

  void finish() {
    json_output["method name"] = "Z3";
  }
};

#endif /* MINISAMPLER_H_ */
