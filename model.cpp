//
// Created by batchen on 03/02/2022.
//

#include "model.h"

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