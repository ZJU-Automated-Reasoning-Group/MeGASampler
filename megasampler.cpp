#include "megasampler.h"
#include "pythonfuncs.h"
#include "strengthen.capnp.h"
#include <iostream>
#include <capnp/serialize.h>
#include <cinttypes>
#include <random>

MEGASampler::MEGASampler(std::string input, int max_samples, double max_time,
                         int max_epoch_samples, double max_epoch_time,
                         int strategy, bool json)
    : Sampler(input, max_samples, max_time, max_epoch_samples, max_epoch_time,
              strategy, json),
      simpl_formula(c) {
  initialize_solvers();
  std::cout << "starting MEGA" << std::endl;
}

void MEGASampler::do_epoch(const z3::model &model) {
	printf("MEGA: do_epoch\n");
	is_time_limit_reached();
    struct buflen ret = call_strengthen(original_formula, model);
    const auto view = kj::arrayPtr(
                                   reinterpret_cast<const capnp::word*>(ret.buf),
                                   ret.len / sizeof(capnp::word));
    capnp::FlatArrayMessageReader message(view);
    auto container = message.getRoot<StrengthenResult>();

    auto res = container.getRes();
    auto failureDescription = container.getFailuredecription();
    if (!res){
        std::cout << "An error has occurred during epoch: " << failureDescription.cStr() << "\n";
        failure_cause = failureDescription.cStr();
        safe_exit(1);
    }
    std::cout << "unsimplified: " << container.getUnsimplified().cStr() << "\n";
    std::cout << "intervals: \n";
	is_time_limit_reached();
    for (auto varinterval : container.getIntervalmap()) {
    	std::string varname = varinterval.getVariable().cStr();
    	auto interval = varinterval.getInterval();
    	bool isLowMinf = interval.getIslowminf();
    	bool isHighInf = interval.getIshighinf();
    	auto low = isLowMinf ? "MINF" : std::to_string(interval.getLow());
    	auto high = isHighInf ? "INF" : std::to_string(interval.getHigh());
    	std::cout << varname << ": " << "[" << low << "," << high << "] ";
    }
    std::cout << "\n";

    sample_intervals_in_rounds(container.getIntervalmap());
}

void MEGASampler::finish() {
	json_output["method name"] = "megasampler";
	Sampler::finish();
}

void MEGASampler::sample_intervals_in_rounds(const auto& intervalmap) {
	int MAX_ROUNDS= 6;
	float rate = 1.0;
	for (int round = 0; round < MAX_ROUNDS && rate > 0.2; round++){
		is_time_limit_reached();
		std::cout << "Starting round: " << round << "\n";
		int new_samples = 0;
		int MAX_SAMPLES = 100;
		int round_samples = 0;
		while (round_samples < MAX_SAMPLES) {
			std::string sample = get_random_sample_from_intervals(intervalmap);
			total_samples++;
			bool is_unique = save_and_output_sample_if_unique(sample);
			if (is_unique){
				new_samples++;
				std::cout << "Found a unique sample. new count is: " << new_samples << "\n";
			}
			round_samples++;
		}
		rate = new_samples / round_samples;
		std::cout << "new rate is: " << rate << "\n";
	}
}

std::string MEGASampler::get_random_sample_from_intervals(const auto& intervalmap){
	std::string sample_string;
	for (auto varinterval : intervalmap) {
		std::string varname = varinterval.getVariable().cStr();
		auto interval = varinterval.getInterval();
		sample_string += varname;
		sample_string += ":";
		int64_t low = interval.getLow();
		int64_t high = interval.getHigh();
		std::mt19937 rng(std::random_device{}());
		std::uniform_int_distribution<int64_t> gen(low, high); // uniform, unbiased
		int64_t randNum = gen(rng);
		sample_string += std::to_string(randNum);
		sample_string += ";";
	}
	std::cout << "generated sample: " << sample_string << "\n";
	return sample_string;
}
