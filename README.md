# MeGASampler
MeGASampler (SMT Sampling Using Model-Guided Approximation)

Paper: TBD

# Previous Work

Based on [SMTSampler](https://github.com/RafaelTupynamba/SMTSampler). See also [GuidedSampler](https://github.com/RafaelTupynamba/GuidedSampler).

# Building

Install dependencies

```
$ sudo apt install git build-essential python3-minimal python3-dev jsoncpp capnproto libcapnp-dev libjsoncpp-dev python3-venv
```

Create Python virtual environment and install Python dependencies

```
$ python -m venv venv
$ source venv/bin/activate
$ pip install --upgrade pip setuptools wheel
$ pip install pycapnp cffi
```

Clone repos

```
$ git clone https://github.com/chaosite/MeGASampler.git
$ git clone https://github.com/chaosite/z3.git # patched z3 for SMTSampler coverage
```

Build patched z3
```
$ pushd z3
$ python scripts/mk_make.py
$ cd build
$ make
$ cd python
$ make install # installs into current Python venv
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
$ ./megasampler -n 1000000 -t 3600 formula.smt2
```

Usage:

```
$ ./megasampler --help
Usage: megasampler [OPTION...] INPUT
megasampler -- Sample SMT formulas

  -b, --blocking             Use blocking instead of random assignment
  -d, --debug                Show debug messages (can be very verbose)
  -e, --epochs=NUM           Number of epochs
  -j, --json                 Write JSON output
  -m, --epoch-samples=NUM    Samples per epoch
  -n, --samples=NUM          Number of samples
  -o, --output-dir=DIRECTORY Output directory (for statistics, samples, ...)
  -r, --epoch-time=SECONDS   Time limit per epoch
  -s, --strategy=STRAT       Strategy: {smtbit, smtbv, sat}
  -t, --time=SECONDS         Time limit
  -x, --smtsampler           Use SMTSampler
  -?, --help                 Give this help list
      --usage                Give a short usage message
  -V, --version              Print program version
```

# Benchmarks

The benchmarks used come from SMT-LIB. They can be obtained from the following repositories:

 * [QF_LIA](https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_LIA)
 * [QF_NIA](https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_NIA)
