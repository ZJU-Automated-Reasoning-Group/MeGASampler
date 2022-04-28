#ifndef STRENGTHENER_H
#define STRENGTHENER_H

#include "intervalmap.h"
#include <z3++.h>

class Strengthener{

    z3::context& c;
    z3::expr& model;
    IntervalMap i_map;

public:
    Strengthener(z3::context& con, z3::expr& mod) : c(con), model(mod) {};
    void strengthen_literal(const z3::expr& literal); // _strengthen_conjunct in python
};

#endif // STRENGTHENER_H
