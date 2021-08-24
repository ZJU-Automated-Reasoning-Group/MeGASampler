.PHONY: all

SRC=$( wildcard *.cpp ) $( wildcard *.h )

all: strengthen.capnp.h $(SRC) pythonfuncs.c
	g++ -g -std=gnu++17 -O3 -o smtsampler strengthen.capnp.c++ smtsampler.cpp pythonfuncs.c megasampler.cpp sampler.cpp main.cpp -I/usr/include/python3.8 -I ../z3/src/api -I ../z3/src/api/c++  -L ../z3/build -L /usr/lib/python3.8/config-3.8m-x86_64-linux-gnu -lz3 -lpython3.8 -lpthread -lcapnp -ljsoncpp
strengthen.capnp.h: strengthen.capnp
	capnp compile -oc++ strengthen.capnp

pythonfuncs.c: pythonfuncs.h python_build.py
	python python_build.py
