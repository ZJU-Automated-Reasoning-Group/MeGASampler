#ifndef SMTSAMPLER_H_
#define SMTSAMPLER_H_

#include <unordered_map>

#include "sampler.h"

class SMTSampler : public Sampler {
  std::vector<z3::func_decl> ind;
  int all_ind_count = 0;
  std::vector<std::pair<int, int>> cons_to_ind;
  std::vector<z3::expr> constraints;
  std::vector<std::vector<z3::expr>> soft_constraints;
  int strategy;
  int flips = 0;
  std::unordered_map<int, std::unordered_set<int>> unsat_ind;
  int unsat_ind_count = 0;

  //  std::unordered_set<Z3_ast> sub;

 public:
  SMTSampler(std::string input, std::string output_dir, int max_samples,
             double max_time, int max_epoch_samples, double max_epoch_time,
             int strategy, bool json, bool blocking);
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
  void finish();

 protected:
  struct Triple {
    std::string a[3] = {"", "", ""};
  };

  std::string model_string(z3::model m, std::vector<z3::func_decl> ind);
  z3::expr value(char const *n, z3::sort s);
  z3::expr value(char const *n);
  long long ll_value(char const *n);
  bool b_value(char const *n);
  void add_constraints(z3::expr exp, z3::expr val, int count);
  void calculate_constraints(const std::string &m_string);
  void find_neighboring_solutions(std::unordered_set<std::string> &mutations);
  void find_combined_solutions(std::unordered_set<std::string> &mutations,
                               const std::string &a_string);
  int combine_mutations(long long val_orig, long long val_b, long long val_c);
  z3::model gen_model(const std::string &candidate,
                      std::vector<z3::func_decl> &ind);
  void assert_is_int_var(const z3::func_decl &v);

  std::string parse_function(std::string const &m_string, size_t &pos,
                             int arity,
                             std::unordered_map<std::string, Triple> &values,
                             int index);
  std::string combine_function(std::string const &str_a,
                               std::string const &str_b,
                               std::string const &str_c, size_t &pos_a,
                               size_t &pos_b, size_t &pos_c, int arity,
                               z3::sort s);
};

#endif /* SMTSAMPLER_H_ */
