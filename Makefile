.PHONY: all clean

BINARY=megasampler
SRC=$(wildcard *.cpp) $(wildcard *.h) $(wildcard *.c++) $(wildcard *.c)
PYVER=$(shell python --version | cut -d. -f1-2 | cut -d' ' -f2)

all: $(BINARY)

CXXFLAGS=-Wall -Wextra -Wshadow -Wnon-virtual-dtor -pedantic -ggdb \
  -std=gnu++17 -march=native -pipe -O3
Z3DIR=../z3
Z3FLAGS=-isystem $(Z3DIR)/src/api -isystem ../z3/src/api/c++ \
 -L ../z3/build -lz3

clean:
	rm -f $(BINARY) testmodel strengthener

$(BINARY): $(SRC)
	g++ $(CXXFLAGS) -o $(BINARY) \
  smtsampler.cpp megasampler.cpp sampler.cpp \
  main.cpp model.cpp strengthener.cpp interval.cpp z3_utils.cpp \
  $(Z3FLAGS) -ljsoncpp -lpthread

testmodel: test_model.cpp model.cpp model.h
	g++ $(CXXFLAGS) -o testmodel \
	test_model.cpp model.cpp \
	$(Z3FLAGS)

strengthener: strengthener.cpp strengthener.h interval.cpp interval.h z3_utils.cpp z3_utils.h test_strengthener.cpp
	g++ $(CXXFLAGS) -o strengthener \
	strengthener.cpp interval.cpp z3_utils.cpp test_strengthener.cpp \
	$(Z3FLAGS)
