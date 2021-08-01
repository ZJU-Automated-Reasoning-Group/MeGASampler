#ifndef SMTSAMPLER_H_
#define SMTSAMPLER_H_

#include "sampler.h"

class SMTSampler : public Sampler {
  std::vector<z3::func_decl> ind;
  int all_ind_count = 0;
  std::vector<std::pair<int, int>> cons_to_ind;
  std::vector<z3::expr> constraints;
  std::vector<std::vector<z3::expr>> soft_constraints;
  int strategy;
//  std::unordered_set<Z3_ast> sub;

public:
  SMTSampler(std::string input, int max_samples, double max_time,
              int max_epoch_samples, double max_epoch_time, int strategy);
  /*
   * Finds additional valid models (samples) of the formula
   * (based on the given model, which is assumed valid).
   * Adds all valid samples to the samples set.
   * Returns the number of new samples found.
   */
  int sample(const z3::model &model);
  /*
   * Saves to the given file a list of all samples found during calls to sample.
   * File should already exist upon calling the function.
   */
  void save_valid_samples(std::string file);
  /*
   * Prints (to stdout) a list of all samples found during calls to sample.
   */
  void print_valid_samples();

  void do_epoch(const z3::model &model);

protected:
  std::string model_string(z3::model m, std::vector<z3::func_decl> ind);
  z3::expr value(char const *n, z3::sort s);
  void add_constraints(z3::expr exp, z3::expr val, int count);
};

#endif /* SMTSAMPLER_H_ */
