#include <argp.h>
#include <unistd.h>

#include <csignal>
#include <cstdlib>
#include <cstring>
#include <memory>

#include "megasampler.h"
#include "pythonfuncs.h"
#include "sampler.h"
#include "smtsampler.h"

const char *argp_program_version = "megasampler 0.1";
const char *argp_program_bug_address = "<mip@cs.technion.ac.il>";

static const char *argp_doc = "megasampler -- Sample SMT formulas";

static const char *argp_args_doc = "INPUT";

static struct argp_option options[] = {
    {"debug", 'd', 0, 0, "Show debug messages (can be very verbose)", 0},
    {"samples", 'n', "NUM", 0, "Number of samples", 0},
    {"time", 't', "SECONDS", 0, "Time limit", 0},
    {"epochs", 'e', "NUM", 0, "Number of epochs", 0},
    {"epoch-samples", 'm', "NUM", 0, "Samples per epoch", 0},
    {"epoch-time", 'r', "SECONDS", 0, "Time limit per epoch", 0},
    {"strategy", 's', "STRAT", 0, "Strategy: {smtbit, smtbv, sat}", 0},
    {"smtsampler", 'x', 0, 0, "Use SMTSampler", 0},
    {"json", 'j', 0, 0, "Write JSON output", 0},
    {"blocking", 'b', 0, 0, "Use blocking instead of random assignment", 0},
    {"output-dir", 'o', "DIRECTORY", 0,
     "Output directory (for statistics, samples, ...)", 0},
    {0, 0, 0, 0, 0, 0}};

struct args {
  char *input;
  char *output_dir = getcwd(NULL, 0);
  unsigned int max_epochs = 1000000, max_samples = 1000000,
               max_epoch_samples = 10000;
  int strategy = STRAT_SMTBIT;
  bool use_smtsampler = false, json = false, blocking = false, debug = false;
  double max_time = 3600.0, max_epoch_time = 600.0;
};

static error_t parse_opt(int key, char *arg, struct argp_state *state) {
  struct args *args = (struct args *)state->input;

  switch (key) {
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
      if (0 == strncmp("sat", arg, 4)) {
        args->strategy = STRAT_SAT;
      } else if (0 == strncmp("smtbit", arg, 7)) {
        args->strategy = STRAT_SMTBIT;
      } else if (0 == strncmp("smtbv", arg, 6)) {
        args->strategy = STRAT_SMTBV;
      } else {
        argp_usage(state);
      }
      break;
    case 'x':
      args->use_smtsampler = true;
      break;
    case 'j':
      args->json = true;
      break;
    case 'b':
      args->blocking = true;
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
static volatile Sampler *global_sampler = NULL;
}

void signal_handler(__attribute__((unused)) int sig) {
  // External timeout
  if (!global_sampler) std::abort();  // This is kinda early...
  global_sampler->set_exit();
}

int main(int argc, char *argv[]) {
  std::signal(SIGHUP, signal_handler);
  struct args args;
  argp_parse(&argp, argc, argv, 0, 0, &args);

  if (args.strategy == STRAT_SAT) {
    std::cout << "Conversion to SAT is temporarily not supported" << std::endl;
    return 0;
  }

  std::unique_ptr<Sampler> s;
  if (args.use_smtsampler) {
    s = std::make_unique<SMTSampler>(
        args.input, args.output_dir, args.max_samples, args.max_time,
        args.max_epoch_samples, args.max_epoch_time, args.strategy, args.json,
        args.blocking);
  } else {
    s = std::make_unique<MEGASampler>(
        args.input, args.output_dir, args.max_samples, args.max_time,
        args.max_epoch_samples, args.max_epoch_time, args.strategy, args.json,
        args.blocking);
  }
  if (args.debug)
    s->debug = true;

  global_sampler = s.get();
  patch_global_context(s->c);
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
      const z3::model &m = s->start_epoch();
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
