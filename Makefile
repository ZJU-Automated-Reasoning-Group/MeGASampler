.PHONY: all clean

BINARY=megasampler
SRC=$(wildcard *.cpp) $(wildcard *.h) $(wildcard *.c++) $(wildcard *.c)
PYVER=$(shell python --version | cut -d. -f1-2 | cut -d' ' -f2)
PYNAME=python$(PYVER)
PYLIBNAME=$(PYNAME)
#PYNAME=pypy3
#PYLIBNAME=pypy3-c

all: $(BINARY)

CXXFLAGS=-Wall -Wextra -Wshadow -Wnon-virtual-dtor -pedantic -ggdb \
  -std=gnu++17 -march=native -pipe -O3
Z3DIR=../z3
Z3FLAGS=-isystem $(Z3DIR)/src/api -isystem ../z3/src/api/c++ \
 -L ../z3/build -lz3

clean:
	rm -f $(BINARY) strengthen.capnp.h pythonfuncs.c strengthen.capnp.c++ testmodel strengthener

$(BINARY): strengthen.capnp.h $(SRC) pythonfuncs.c
	g++ $(CXXFLAGS) -o $(BINARY) \
  strengthen.capnp.c++ smtsampler.cpp pythonfuncs.c megasampler.cpp sampler.cpp \
  main.cpp model.cpp \
  -isystem /usr/lib/$(PYNAME)/include -isystem /usr/include/$(PYNAME) \
  $(Z3FLAGS) -L /usr/lib/$(PYNAME)/config-$(PYVER)m-x86_64-linux-gnu \
  -lz3 -l$(PYLIBNAME) -lpthread -lcapnp -ljsoncpp

strengthen.capnp.h: strengthen.capnp
	capnp compile -oc++ strengthen.capnp

pythonfuncs.c: pythonfuncs.h python_build.py
	$(PYNAME) python_build.py

testmodel: test_model.cpp model.cpp model.h
	g++ $(CXXFLAGS) -o testmodel \
	test_model.cpp model.cpp \
	$(Z3FLAGS)

strengthener: strengthener.cpp strengthener.h interval.cpp interval.h z3_utils.cpp z3_utils.h test_strengthener.cpp
	g++ $(CXXFLAGS) -o strengthener \
	strengthener.cpp interval.cpp z3_utils.cpp test_strengthener.cpp \
	$(Z3FLAGS)

