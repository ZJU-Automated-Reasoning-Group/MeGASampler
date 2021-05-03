all:
	g++ -g -std=gnu++17 -O3 -o smtsampler smtsampler.cpp megasampler.cpp sampler.cpp pythoncaller.cpp main.cpp -I/usr/include/python3.9 -L ../z3/build -lz3 -lpython3.9
