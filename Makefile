.PHONY: all

SRC=$( wildcard *.cpp ) $( wildcard *.h )

all: samples.capnp.h $(SRC) pythonfuncs.c
	g++ -g -std=gnu++17 -O3 -o smtsampler samples.capnp.c++ smtsampler.cpp pythonfuncs.c megasampler.cpp sampler.cpp main.cpp -I/usr/include/python3.9 -L ../z3/build -lz3 -lpython3.9 -lpthread -lcapnp

samples.capnp.h: samples.capnp
	capnp compile -oc++ samples.capnp

pythonfuncs.c: pythonfuncs.h python_build.py
	python python_build.py
