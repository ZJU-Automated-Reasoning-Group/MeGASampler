# SMTSampler
MeGASampler (SMT Sampling Using Model-Guided Approximation)

Paper: TBD

# Previous Work

Based on [SMTSampler](https://github.com/RafaelTupynamba/SMTSampler). See also [GuidedSampler](https://github.com/RafaelTupynamba/GuidedSampler).

# Building

Install dependencies

```
sudo apt install git build-essential python3-minimal python3-dev jsoncpp capnproto libcapnp-dev libjsoncpp-dev python3-venv
```

Create Python virtual environment and install Python dependencies

```
python -m venv venv
source venv/bin/activate
pip install --upgrade pip setuptools wheel
pip install pycapnp
```

Clone repos

```
git clone https://github.com/chaosite/MeGASampler.git
git clone https://github.com/chaosite/z3.git # patched z3 for SMTSampler coverage
```

Build patched z3
```
pushd z3
python scripts/mk_make.py
cd build
make
cd python
make install # installs into current Python venv
popd
```

Build SMTSampler

```
cd SMTSampler
make
```

# Running

Simply run with

```
./smtsampler -n 1000000 -t 3600 formula.smt2
```

# Benchmarks

The benchmarks used come from SMT-LIB. They can be obtained from the following repositories.

[QF_LIA](https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_LIA)
[QF_NIA](https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_NIA)
