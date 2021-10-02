.PHONY: all

SRC=$( wildcard *.cpp ) $( wildcard *.h )
PYVER=3.9
PYNAME=python$(PYVER)
PYLIBNAME=$(PYNAME)
#PYNAME=pypy3
#PYLIBNAME=pypy3-c

all: strengthen.capnp.h $(SRC) pythonfuncs.c
	g++ -Wall -Wextra -Wshadow -Wnon-virtual-dtor -pedantic -ggdb -std=gnu++17 -O3 -o smtsampler strengthen.capnp.c++ smtsampler.cpp pythonfuncs.c megasampler.cpp sampler.cpp main.cpp -isystem /usr/lib/$(PYNAME)/include -isystem /usr/include/$(PYNAME) -isystem ../z3/src/api -isystem ../z3/src/api/c++  -L ../z3/build -L /usr/lib/$(PYNAME)/config-$(PYVER)m-x86_64-linux-gnu -lz3 -l$(PYLIBNAME) -lpthread -lcapnp -ljsoncpp
strengthen.capnp.h: strengthen.capnp
	capnp compile -oc++ strengthen.capnp

pythonfuncs.c: pythonfuncs.h python_build.py
	$(PYNAME) python_build.py
