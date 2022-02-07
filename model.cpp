//
// Created by batchen on 03/02/2022.
//

#include <random>
#include "model.h"

static inline int64_t draw_random_int(){
    std::mt19937 rng(std::random_device{}());
    std::uniform_int_distribution<int64_t> gen(INT64_MIN,INT64_MAX);  // uniform, unbiased
    return gen(rng);
}

bool Model::addIntAssignment(const std::string & var, int value){
    std::pair<std::map<std::string,int>::iterator,bool> ret;
    ret = variable_map.insert(std::pair<std::string,int>(var,value));
    return ret.second;
}

bool Model::addArrayAssignment(const std::string & array, int index, int value){
    std::pair<std::map<std::string, std::map<int, int>>::iterator,bool> ret;
    std::map<int,int> idx_val_map;
    idx_val_map.insert ( std::pair<int,int>(index, value) );
    ret = array_map.insert(std::pair<std::string, std::map<int, int>>(array,idx_val_map));
    if (ret.second){ // array not in map
        return ret.second;
    } else { // array in map, but maybe index isn't
        std::pair<std::map<int, int>::iterator,bool> ret2;
        ret2 = ret.first->second.insert(std::pair<int,int>(index, value));
        return ret2.second;
    }
}

std::string Model::toString(){
    std::string res;
    for (std::map<std::string,int>::iterator  it=variable_map.begin(); it!=variable_map.end(); ++it){
        res += it->first;
        res += ":";
        res += std::to_string(it->second);
        res += ";";
    }
    for (std::map<std::string,std::map<int,int>>::iterator  it=array_map.begin(); it!=array_map.end(); ++it){
        res += it->first;
        res += "::";
        std::map<int,int> idx_val_map = it->second;
        for (std::map<int,int>::iterator it2=idx_val_map.begin(); it2!=idx_val_map.end(); it2++){
            res += std::to_string(it2->first);
            res += ":";
            res += std::to_string(it2->second);
            res += ",";
        }
        res += ";";
    }
    return res;
}

std::pair<int,bool> Model::evalIntVar(const std::string & var){
    auto it = variable_map.find(var);
    if (it == variable_map.end()){
        return std::pair<int,bool>(-1, false);
    } else {
        return std::pair<int,bool>(it->second, true);
    }
}

std::pair<int,bool> Model::evalArrayVar(const std::string &array, int index) {
    auto it = array_map.find(array);
    if (it == array_map.end()){
        return std::pair<int,bool>(-1, false);
    } else {
        auto & curr_array_map = it->second;
        auto it2 = curr_array_map.find(index);
        if (it2 == curr_array_map.end()){
            return std::pair<int,bool>(-1, false);
        } else {
            return std::pair<int,bool>(it2->second, true);
        }
    }
}

std::pair<int,bool> Model::evalIntExpr(const z3::expr & e, bool debug, bool model_completion){
    assert(z3::is_int(e));
    assert(e.is_app());
    z3::func_decl fd = e.decl();
    if (e.is_const()) {
        int i;
        if (e.is_numeral_i(i)){
            if (debug) std::cout << "found numeral: " << std::to_string(i) << "\n";
            return std::pair<int,bool>(i, true);
        }
        std::string name = fd.name().str();
        if (debug) std::cout << "found const: " << name << "\n";
        auto res = evalIntVar(name);
        if (model_completion && !res.second){
            int64_t rand = draw_random_int();
            auto r = addIntAssignment(name, rand);
            assert(r);
            return std::pair<int, bool>(rand, true);
        } else {
            return res;
        }
    } else if (fd.decl_kind() == Z3_OP_SELECT){
        auto array = e.arg(0);
        auto index = e.arg(1);
        std::pair<int, bool> index_res = evalIntExpr(index, debug);
        if (index_res.second){
            std::string array_name = array.decl().name().str();
            auto res = evalArrayVar(array_name,index_res.first);
            if (model_completion && !res.second){
                int64_t rand = draw_random_int();
                auto r = addArrayAssignment(array_name, index_res.first, rand);
                assert(r);
                return std::pair<int, bool>(rand, true);
            } else {
                return res;
            }
        } else {
            return index_res;
        }
    }
    std::vector<int> children_values;
    for (unsigned int i=0; i < e.num_args(); i++){
        auto arg = e.arg(i);
        std::pair<int,bool> res_arg = evalIntExpr(arg, debug);
        if (!res_arg.second){
            return res_arg;
        } else {
            children_values.push_back(res_arg.first);
        }
    }
    switch (fd.decl_kind()) {
        case Z3_OP_ADD: {
            if (debug) std::cout << "found add\n";
            int sum = 0;
            for (std::vector<int>::iterator it = children_values.begin(); it != children_values.end(); ++it) {
                sum += *it;
            }
            return std::pair<int, bool>(sum, true);
        }
        case Z3_OP_MUL: {
            if (debug) std::cout << "found mul\n";
            int prod = 1;
            for (std::vector<int>::iterator it = children_values.begin(); it != children_values.end(); ++it) {
                prod *= *it;
            }
            return std::pair<int, bool>(prod, true);
        }
        case Z3_OP_SUB: {
            if (debug) std::cout << "found sub\n";
            assert(children_values.size() == 2);
            return std::pair<int, bool>(children_values[0] - children_values[1], true);
        }
        case Z3_OP_UMINUS: {
            if (debug) std::cout << "found uminus\n";
            assert(children_values.size() == 1);
            return std::pair<int, bool>(-children_values[0], true);
        }
        default:{
            if (debug) std::cout << "unknown op: " << fd.decl_kind() << "\n";
            return std::pair<int,bool>(-1, false);
        }
    }
}
