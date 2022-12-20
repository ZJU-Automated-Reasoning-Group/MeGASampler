
# NOTE:

I moved some code in https://github.com/ZJU-Automated-Reasoning-Group/smt_sampler to this repo. (e.g., `z3_plus.h`, `file_system.h`, `region_sampler.h`)
However, the features have not beed tested.


# MeGASampler
MeGASampler (SMT Sampling Using Model-Guided Approximation), FM'2023

# Previous Work

Based on [SMTSampler](https://github.com/RafaelTupynamba/SMTSampler). See also [GuidedSampler](https://github.com/RafaelTupynamba/GuidedSampler).

# Building

Install dependencies

```
$ sudo apt install git build-essential python3-minimal python3-dev jsoncpp libjsoncpp-dev python3-venv
```

Create Python virtual environment and install Python dependencies

```
$ python -m venv venv --upgrade # consider using pypy
$ source venv/bin/activate
```

Clone repos

```
$ git clone https://github.com/chaosite/MeGASampler.git
$ git clone https://github.com/chaosite/z3.git # patched z3 for SMTSampler coverage
```

Build patched z3
```
$ pushd z3
$ python scripts/mk_make.py --python
$ cd build
$ make # consider adding -j$(nproc)
$ cd python
$ make install # installs into current Python venv, do *not* use sudo
$ popd
```

Build MeGASampler

```
$ cd MeGASampler
$ make
```

# Running

tl;dr:

```
$ export LD_LIBRARY_PATH="venv/lib"
$ ./megasampler -n 1000000 -a MeGA -t 3600 formula.smt2
```

Usage:

```
$ ./megasampler --help
Usage: megasampler [OPTION...] INPUT
megasampler -- Sample SMT formulas

  -1, --one-epoch            Run all algorithms for one epoch
  -a, --algorithm=ALGORITHM  Select which sampling algorithm to use {MeGA,
                             MeGAb, SMT, z3}
  -d, --debug                Show debug messages (can be very verbose)
  -e, --epochs=NUM           Number of epochs
  -j, --json                 Write JSON output
  -m, --epoch-samples=NUM    Samples per epoch
  -n, --samples=NUM          Number of samples
  -o, --output-dir=DIRECTORY Output directory (for statistics, samples, ...)
  -r, --epoch-time=SECONDS   Time limit per epoch
  -s, --strategy=STRAT       Strategy: {smtbit, smtbv, sat}
  -t, --time=SECONDS         Time limit
  -?, --help                 Give this help list
      --usage                Give a short usage message
  -V, --version              Print program version
```

# Benchmarks

The benchmarks used come from SMT-LIB. They can be obtained from the following
repositories:

 * [QF_LIA](https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_LIA)
 * [QF_NIA](https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_NIA)
