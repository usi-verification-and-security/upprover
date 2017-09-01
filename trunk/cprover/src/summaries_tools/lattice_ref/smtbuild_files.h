/* 
 * File:   smtbuild_filest.h
 * Author: karinek
 *
 * Created on 12 May 2017, 10:39
 */

#ifndef SMTBUILD_FILEST_H
#define SMTBUILD_FILEST_H

#include <set>
#include <iostream>
#include <fstream>
using namespace std;

class smtbuild_filest {
public:
    smtbuild_filest(){}
    smtbuild_filest(
        std::string filename_decls, 
        std::string filename_facts,
        std::string filename_facts2impl)
    { init_smtbuild_data(filename_decls, filename_facts,filename_facts2impl);}
    virtual ~smtbuild_filest() {}
    
    int smtwrite_implication_tests(std::string test_path);
    
private:
    std::set<std::string> decls;
    std::set<std::string> facts;
    std::set<std::string> facts2impl;
    
    void init_smtbuild_data(std::string f_decls, std::string f_facts, std::string f_facts2i);
};

#endif /* SMTBUILD_FILEST_H */

