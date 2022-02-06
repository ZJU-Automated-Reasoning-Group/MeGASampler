//
// Created by batchen on 03/02/2022.
//

#ifndef MEGASAMPLER_MODEL_H
#define MEGASAMPLER_MODEL_H

#include <map>
#include <string>
#include <vector>
#include <iostream>
#include <z3++.h>

class Model {
    std::map<std::string, int> variable_map;
    std::map<std::string, std::map<int, int>> array_map;
public:
    // Returns true iff assignment was successful (i.e, var was not previously assigned).
    bool addIntAssignment(const std::string & var, int value);
    // Returns true iff assignment was successful (i.e, array[index] was not previously assigned).
    bool addArrayAssignment(const std::string & array, int index, int value);
    std::string toString();
    /*
     * If var is assigned in the current model - returns its value in the model and true.
     * Else - returns -1 and false.
     * */
    std::pair<int,bool> evalIntVar(const std::string & var);
    /*
     * If array[index] is assigned in the current model - returns its value in the model and true.
     * Else - returns -1 and false.
     * */
    std::pair<int,bool> evalArrayVar(const std::string & array, int index);
    /*
     * If all variables in e are assigned in the current model - returns the value of e in the model and true.
     * Else - returns -1 and false.
     * */
    std::pair<int,bool> evalIntExpr(const z3::expr & e, bool debug = false);
};

#endif //MEGASAMPLER_MODEL_H
