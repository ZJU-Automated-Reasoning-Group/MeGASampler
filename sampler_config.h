/* -*-c++-*- */

#ifndef SAMPLER_CONFIG_H
#define SAMPLER_CONFIG_H

#include <string>

namespace MeGA {

enum algorithm { ALGO_UNSET = 0, ALGO_MEGA, ALGO_MEGAB, ALGO_SMT, ALGO_Z3 };
enum { STRAT_SMTBIT, STRAT_SMTBV, STRAT_SAT };

struct SamplerConfig {
  SamplerConfig(bool blocking, bool one_epoch, bool debug, bool exhaust_epoch,
                bool interval_size, bool avoid_maxsmt,
                unsigned long max_samples, unsigned long max_epoch_samples,
                unsigned long max_time, unsigned long max_epoch_time,
                unsigned long strategy, bool json, bool no_write,
                double min_rate, unsigned long num_rounds)
      : blocking(blocking),
        one_epoch(one_epoch),
        debug(debug),
        exhaust_epoch(exhaust_epoch),
        interval_size(interval_size),
        avoid_maxsmt(avoid_maxsmt),
        json(json),
        no_write(no_write),
        max_samples(max_samples),
        max_epoch_samples(max_epoch_samples),
        max_time(max_time),
        max_epoch_time(max_epoch_time),
        strategy(strategy),
        min_rate(min_rate),
        num_rounds(num_rounds) {}

  const bool blocking;
  const bool one_epoch;
  const bool debug;
  const bool exhaust_epoch;
  const bool interval_size;
  const bool avoid_maxsmt;
  const bool json;
  const bool no_write;
  const unsigned long max_samples;
  const unsigned long max_epoch_samples;
  const unsigned long max_time;
  const unsigned long max_epoch_time;
  const unsigned long strategy;
  const double min_rate;
  const unsigned long num_rounds;
};

}  // namespace MeGA

#endif
