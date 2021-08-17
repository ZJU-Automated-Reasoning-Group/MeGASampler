#include "megasampler.h"
#include "pythonfuncs.h"
#include "samples.capnp.h"
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
    auto container = message.getRoot<SampleContainer>();

    for (auto sample : container.getSamples()) {
        for (const auto variable : sample.getVariables()) {
            const auto symbol(variable.getSymbol().cStr());
            int64_t value = variable.getValue();
            printf("%s: %" PRIi64 ", ", symbol, value);
        }
        printf("\n");
    }
}
