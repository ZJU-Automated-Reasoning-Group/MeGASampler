#include "megasampler.h"
#include "pythonfuncs.h"
#include "strengthen.capnp.h"
#include <iostream>
#include <capnp/serialize.h>
#include <cinttypes>

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

}

void MEGASampler::finish() {
	json_output["method name"] = "megasampler";
	Sampler::finish();
}
