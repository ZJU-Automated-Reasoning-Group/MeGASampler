/*
 * file_system.h
 *      Author: rainoftime
 */
#ifndef FILESYSTEM_H_
#define FILESYSTEM_H_
#include <string>
#include <vector>
#include <map>
#include <ctime>
#include <fstream>
#include <iostream>
#include <glob.h>
#include <dirent.h>
#include <cstring>

using namespace std;
// E.g.  pattern is /home/rot/*.smt2
void get_files(const string& pattern, vector<string>& files){
    glob_t glob_result;
    glob(pattern.c_str(),GLOB_TILDE,NULL,&glob_result);
    for(unsigned int i=0; i<glob_result.gl_pathc; ++i){
        files.push_back(string(glob_result.gl_pathv[i]));
    }
    globfree(&glob_result);
}

bool file_exists(char* filename) {
    struct stat buf;
    if (stat(filename, &buf) != -1) {
        return true;
    }
    return false;
}

#endif /* FILESYSTEM_H_ */
