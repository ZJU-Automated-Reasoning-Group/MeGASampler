.PHONY: all clean tidy

BINARY=megasampler
SRC=$(wildcard *.cpp) $(wildcard *.h) $(wildcard *.c++) $(wildcard *.c)
OBJS=sampler.o megasampler.o smtsampler.o interval.o intervalmap.o \
 model.o strengthener.o z3_utils.o main.o
DEPS=$(OBJS:%.o=%.d)

PYVER=$(shell python --version | cut -d. -f1-2 | cut -d' ' -f2)

all: $(BINARY)

CXXFLAGS=-Wall -Wextra -Wnon-virtual-dtor -pedantic -ggdb \
  -std=gnu++17 -march=native -pipe -O3 -flto
Z3DIR=../z3
Z3FLAGS=-isystem $(Z3DIR)/src/api -isystem ../z3/src/api/c++
Z3LINKFLAGS=-L ../z3/build -lz3

clean:
	rm -f $(BINARY) $(OBJS) $(DEPS) testmodel strengthener

tidy:
	clang-tidy *.cpp -- $(CXXFLAGS) $(Z3FLAGS)

%.o: %.cpp
	$(CC) $(CFLAGS) $(CXXFLAGS) $(Z3FLAGS) -MMD -c $<

-include $(DEPS)

$(BINARY): $(OBJS)
	g++ $(CXXFLAGS) -o $(BINARY) \
  $(OBJS) \
  $(Z3LINKFLAGS) -ljsoncpp -lpthread

testmodel: test_model.cpp model.cpp model.h
	g++ $(CXXFLAGS) -o testmodel \
	test_model.cpp model.cpp \
	$(Z3FLAGS)

strengthener: strengthener.cpp strengthener.h interval.cpp interval.h z3_utils.cpp z3_utils.h test_strengthener.cpp
	g++ $(CXXFLAGS) -o strengthener \
	strengthener.cpp interval.cpp z3_utils.cpp test_strengthener.cpp \
	$(Z3FLAGS)
