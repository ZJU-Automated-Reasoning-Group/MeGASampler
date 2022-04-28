.PHONY: all clean

BINARY=megasampler
SRC=$(wildcard *.cpp) $(wildcard *.h) $(wildcard *.c++) $(wildcard *.c)
PYVER=3.9
PYNAME=python$(PYVER)
PYLIBNAME=$(PYNAME)
#PYNAME=pypy3
#PYLIBNAME=pypy3-c

all: $(BINARY)

clean:
	rm -f $(BINARY) strengthen.capnp.h pythonfuncs.c strengthen.capnp.c++ testmodel strengthener

$(BINARY): strengthen.capnp.h $(SRC) pythonfuncs.c
	g++ -Wall -Wextra -Wshadow -Wnon-virtual-dtor -pedantic -ggdb \
  -std=gnu++17 -march=native -pipe -O3 -o $(BINARY) \
  strengthen.capnp.c++ smtsampler.cpp pythonfuncs.c megasampler.cpp sampler.cpp \
  main.cpp model.cpp\
  -isystem /usr/lib/$(PYNAME)/include -isystem /usr/include/$(PYNAME) \
  -isystem ../z3/src/api -isystem ../z3/src/api/c++  \
  -L ../z3/build -L /usr/lib/$(PYNAME)/config-$(PYVER)m-x86_64-linux-gnu \
  -lz3 -l$(PYLIBNAME) -lpthread -lcapnp -ljsoncpp

strengthen.capnp.h: strengthen.capnp
	capnp compile -oc++ strengthen.capnp

pythonfuncs.c: pythonfuncs.h python_build.py
	$(PYNAME) python_build.py

testmodel: test_model.cpp model.cpp model.h
	g++ -Wall -Wextra -Wshadow -Wnon-virtual-dtor -pedantic -ggdb \
  	-std=gnu++17 -march=native -pipe -O3 -o testmodel \
  	test_model.cpp model.cpp \
      -isystem ../z3/src/api -isystem ../z3/src/api/c++  \
      -L ../z3/build -lz3

strengthener: strengthener.cpp strengthener.h intervalmap.cpp intervalmap.h z3_utils.cpp z3_utils.h
	g++ -Wall -Wextra -Wnon-virtual-dtor -pedantic -ggdb \
      	-std=gnu++17 -march=native -pipe -O3 -o strengthener \
      	strengthener.cpp intervalmap.cpp z3_utils.cpp \
          -isystem ../z3/src/api -isystem ../z3/src/api/c++  \
          -L ../z3/build -lz3