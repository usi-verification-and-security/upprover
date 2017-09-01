/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   facts_smt.h
 * Author: karinek
 *
 * Created on 31 August 2017, 10:32
 */

#ifndef FACTS_SMT_H
#define FACTS_SMT_H

#include "facts.h"

class facts_smtt : public factst {
public:
    facts_smtt() {}
    
    virtual ~facts_smtt() {}
    
    virtual bool load_facts(std::string file_name);
    
    virtual std::string get_declare_original_function() { return declare_original_function; }
    virtual std::string get_original_function_name() { return original_function_name; }
    virtual std::string get_original_header_function() { return original_header_function; }
    virtual bool is_return_value_unsigned() { return is_return_unsigned; }
    virtual std::string get_params_set_of_function() { return params_set_of_function;}
    
private:
    std::string original_function_name; // Name of the refined function: mod (e.g.,)
    std::string declare_original_function; // declare only of the fuction: (declare-fun |_mod#0| (Real Real) Real)
    std::string original_header_function; // in/out parameters and return value type
    std::string params_set_of_function; // Which parameters we will use (e.g., a, n for mode)
    
    bool is_return_unsigned;
};

#endif /* FACTS_SMT_H */

