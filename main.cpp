#include <argp.h>
#include <unistd.h>

#include <csignal>
#include <cstdlib>
#include <cstring>
#include <memory>

#include "megasampler.h"
#include "minisampler.h"
#include "pythonfuncs.h"
#include "sampler.h"
#include "smtsampler.h"

const char *argp_program_version = "megasampler 0.1";
const char *argp_program_bug_address = "<mip@cs.technion.ac.il>";

static const char *argp_doc = "megasampler -- Sample SMT formulas";

static const char *argp_args_doc = "INPUT";
enum algorithm { ALGO_UNSET = 0, ALGO_MEGA, ALGO_MEGAB, ALGO_SMT, ALGO_Z3 };

static struct argp_option options[] = {
    {"algorithm", 'a', "ALGORITHM", 0,
     "Select which sampling algorithm to use {MeGA, MeGAb, SMT, z3}", 0},
    {"one-epoch", '1', 0, 0, "Run all algorithms for one epoch", 0},
    {"debug", 'd', 0, 0, "Show debug messages (can be very verbose)", 0},
    {"samples", 'n', "NUM", 0, "Number of samples", 0},
    {"time", 't', "SECONDS", 0, "Time limit", 0},
    {"epochs", 'e', "NUM", 0, "Number of epochs", 0},
    {"epoch-samples", 'm', "NUM", 0, "Samples per epoch", 0},
    {"epoch-time", 'r', "SECONDS", 0, "Time limit per epoch", 0},
    {"strategy", 's', "STRAT", 0, "Strategy: {smtbit, smtbv, sat}", 0},
    {"json", 'j', 0, 0, "Write JSON output", 0},
    {"output-dir", 'o', "DIRECTORY", 0,
     "Output directory (for statistics, samples, ...)", 0},
    {0, 0, 0, 0, 0, 0}};

struct args {
  char *input;
  std::string output_dir{getcwd(NULL, 0)};
  unsigned int max_epochs = 1000000, max_samples = 1000000,
               max_epoch_samples = 10000;
  enum algorithm algorithm = ALGO_UNSET;
  int strategy = STRAT_SMTBIT;
  bool json = false, debug = false, one_epoch = false;
  double max_time = 3600.0, max_epoch_time = 600.0;
};

static error_t parse_opt(int key, char *arg, struct argp_state *state) {
  struct args *args = (struct args *)state->input;

  switch (key) {
    case 'a':
      if (0 == strncasecmp("mega", arg, 5))
        args->algorithm = ALGO_MEGA;
      else if (0 == strncasecmp("megab", arg, 6))
        args->algorithm = ALGO_MEGAB;
      else if (0 == strncasecmp("smt", arg, 4))
        args->algorithm = ALGO_SMT;
      else if (0 == strncasecmp("z3", arg, 3))
        args->algorithm = ALGO_Z3;
      break;
    case '1':
      args->one_epoch = true;
      break;
    case 'd':
      args->debug = true;
      break;
    case 'n':
      args->max_samples = atoi(arg);
      break;
    case 't':
      args->max_time = atof(arg);
      break;
    case 'e':
      args->max_epochs = atoi(arg);
      break;
    case 'r':
      args->max_epoch_time = atof(arg);
      break;
    case 'm':
      args->max_samples = atoi(arg);
      break;
    case 's':
      if (0 == strncasecmp("sat", arg, 4)) {
        args->strategy = STRAT_SAT;
      } else if (0 == strncasecmp("smtbit", arg, 7)) {
        args->strategy = STRAT_SMTBIT;
      } else if (0 == strncasecmp("smtbv", arg, 6)) {
        args->strategy = STRAT_SMTBV;
      } else {
        argp_usage(state);
      }
      break;
    case 'j':
      args->json = true;
      break;
    case 'o':
      args->output_dir = arg;
      break;
    case ARGP_KEY_END:
      if (state->arg_num < 1) argp_usage(state);
      break;
    case ARGP_KEY_ARG:
      if (state->arg_num >= 1) argp_usage(state);

      args->input = arg;
      break;
    default:
      return ARGP_ERR_UNKNOWN;
  }
  return 0;
}

static struct argp argp = {options, parse_opt, argp_args_doc, argp_doc, 0,
                           0,       0};

namespace {
static volatile Sampler *volatile global_samplers[4] = {
    NULL,
};
}

void signal_handler(__attribute__((unused)) int sig) {
  // External timeout
  if (NULL == global_samplers[0]) std::abort();
  for (unsigned long i = 0;
       i < sizeof(global_samplers) / sizeof(*global_samplers); ++i) {
    global_samplers[i]->set_exit();
  }
}

int regular_run(z3::context &c, const struct args &args) {
  std::unique_ptr<Sampler> s;

  switch (args.algorithm) {
    case ALGO_UNSET:
      std::cout << "Please select an algorithm\n";
      exit(1);
      break;
    case ALGO_MEGA:
      s = std::make_unique<MEGASampler>(
          &c, args.input, args.output_dir, args.max_samples, args.max_time,
          args.max_epoch_samples, args.max_epoch_time, args.strategy, args.json,
          false);
      break;
    case ALGO_MEGAB:
      s = std::make_unique<MEGASampler>(
          &c, args.input, args.output_dir, args.max_samples, args.max_time,
          args.max_epoch_samples, args.max_epoch_time, args.strategy, args.json,
          true);
      break;
    case ALGO_SMT:
      s = std::make_unique<SMTSampler>(
          &c, args.input, args.output_dir, args.max_samples, args.max_time,
          args.max_epoch_samples, args.max_epoch_time, args.strategy, args.json,
          false);
      break;
    case ALGO_Z3:
      s = std::make_unique<MiniSampler>(
          &c, args.input, args.output_dir, args.max_samples, args.max_time,
          args.max_epoch_samples, args.max_epoch_time, args.strategy, args.json,
          false);
      break;
  }
  if (args.debug) s->debug = true;

  global_samplers[0] = s.get();
  patch_global_context(c);
  s->set_timer_max("total", args.max_time);
  s->set_timer_max("epoch", args.max_epoch_time);
  s->set_timer_on("total");
  s->set_timer_on("initial_solving");
  s->check_if_satisfiable();  // todo: save model from initial solving?
  s->accumulate_time("initial_solving");
  try {
    for (size_t epochs = 0; epochs < args.max_epochs; epochs++) {
      s->set_timer_on("epoch");
      s->set_timer_on("start_epoch");
      z3::model m = s->start_epoch();
      s->accumulate_time("start_epoch");
      s->set_timer_on("do_epoch");
      s->do_epoch(m);
      s->accumulate_time("do_epoch");
      s->accumulate_time("epoch");
    }
  } catch (const z3::exception &except) {
    std::cout << "Termination due to: " << except << "\n";
  }
  s->accumulate_time("total");
  s->safe_exit(0);
  return 0;
}

int one_epoch_run(z3::context &c, const struct args &args) {
  std::unique_ptr<Sampler> samplers[] = {
      std::make_unique<MEGASampler>(&c, args.input, args.output_dir + "/MeGA",
                                    args.max_samples, args.max_time,
                                    args.max_epoch_samples, args.max_epoch_time,
                                    args.strategy, args.json, false),
      std::make_unique<MEGASampler>(&c, args.input, args.output_dir + "/MeGAb",
                                    args.max_samples, args.max_time,
                                    args.max_epoch_samples, args.max_epoch_time,
                                    args.strategy, args.json, true),
      std::make_unique<SMTSampler>(&c, args.input, args.output_dir + "/SMT",
                                   args.max_samples, args.max_time,
                                   args.max_epoch_samples, args.max_epoch_time,
                                   args.strategy, args.json, false),
      std::make_unique<MiniSampler>(&c, args.input, args.output_dir + "/Z3",
                                    args.max_samples, args.max_time,
                                    args.max_epoch_samples, args.max_epoch_time,
                                    args.strategy, args.json, false)};

  for (unsigned int i = 0; i < sizeof(samplers) / sizeof(*samplers); ++i) {
    global_samplers[i] = samplers[i].get();
    samplers[i]->set_timer_max("total", args.max_time);
    samplers[i]->set_timer_max("epoch", args.max_epoch_time);
    samplers[i]->set_timer_on("total");
    samplers[i]->set_timer_on("initial_solving");
  }

  samplers[0]->check_if_satisfiable();

  for (unsigned int i = 0; i < sizeof(samplers) / sizeof(*samplers); ++i) {
    samplers[i]->accumulate_time("initial_solving");
    samplers[i]->set_timer_on("epoch");
    samplers[i]->set_timer_on("start_epoch");
  }

  z3::model m = samplers[0]->start_epoch();

  for (unsigned int i = 0; i < sizeof(samplers) / sizeof(*samplers); ++i) {
    samplers[i]->accumulate_time("start_epoch");
    samplers[i]->accumulate_time("epoch");
    samplers[i]->accumulate_time("total");
  }

  for (unsigned int i = 0; i < sizeof(samplers) / sizeof(*samplers); ++i) {
    /* make sure to output the solution from start_epoch */
    samplers[i]->save_and_output_sample_if_unique(
        samplers[i]->model_to_string(m));

    samplers[i]->set_timer_on("total");
    samplers[i]->set_timer_on("epoch");
    samplers[i]->set_timer_on("do_epoch");
    samplers[i]->set_model(m);
    try {
      samplers[i]->do_epoch(m);
    } catch (const z3::exception &e) {
      std::cout << "Failed in Sampler " << i << " due to: " << e << "\n";
    }
    samplers[i]->accumulate_time("do_epoch");
    samplers[i]->accumulate_time("epoch");
    samplers[i]->accumulate_time("total");

    samplers[i]->finish();  // All done :)
  }

  return 0;
}

int main(int argc, char *argv[]) {
  std::signal(SIGHUP, signal_handler);
  struct args args;
  argp_parse(&argp, argc, argv, 0, 0, &args);

  if (args.strategy == STRAT_SAT) {
    std::cout << "Conversion to SAT is temporarily not supported\n";
    return 1;
  }

  if (args.one_epoch && args.algorithm != ALGO_UNSET) {
    std::cout << "Can't choose an algorithm in one-epoch mode.";
    return 1;
  }

  z3::context c;

  if (!args.one_epoch) return regular_run(c, args);
  return one_epoch_run(c, args);
}
