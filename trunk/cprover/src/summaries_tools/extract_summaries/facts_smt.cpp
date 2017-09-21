/* 
 * File:   facts_smt.cpp
 * Author: karinek
 * 
 * Created on 31 August 2017, 10:32
 */

#include "facts_smt.h"

#include <iostream>
#include <fstream>
using namespace std;

/*******************************************************************

 Function: facts_smtt::load_facts

 Inputs: file name in this format, e.g., mod function
 * mod
 * (declare-fun |_mod#0| (Real Real) Real)
 * ((|mod::a!0| Real) (|mod::n!0| Real) (|hifrog::fun_start| Bool) (|hifrog::fun_end| Bool) (|mod::#return_value!0| Real) ) Bool
 * true

 Outputs: false if didn't load the file

 Purpose: 

\*******************************************************************/
bool facts_smtt::load_facts(std::string file_name) {    
    std::ifstream input(file_name);
     if (!input.is_open()) {
        std::cout << "Cannot open the file: " <<  file_name << std::endl;
        return false;
     }
    
    // Read the file
    string line = "";
    
    // Name of the original function. E.g., mod
    if (!std::getline(input, line)) {
        std::cout << "Error reading original_function_name \n";
        return false;
    }
    original_function_name = line;
    std::cout << "Start loading " << file_name << " function's facts: " << original_function_name << std::endl;
 
    
    // Declare of the original function
    if (!std::getline(input, line)) {
        std::cout << "Error reading declare_original_function \n";
        return false;
    }
    declare_original_function = line;
    
    // Define part of the original function header
    if (!std::getline(input, line)) {
        std::cout << "Error reading original_header_function \n";
        return false;
    }
    original_header_function = line;    
    
    // Define part of the original function header
    if (!std::getline(input, line)) {
        std::cout << "Error reading is_return_unsigned \n";
        return false;
    }
    is_return_unsigned = (line.find("true") != std::string::npos); 
    
    // in/out parameters of the facts
    if (!std::getline(input, line)) {
        std::cout << "Error reading params_set_of_function \n";
        return false;
    }
    params_set_of_function = line;  
    
    
    // Load the rest of the facts
    std::string name="";
    std::string fact="";
    std::cout << "==> Reading facts: ";
    while (std::getline(input, name)) {
        if (name[0] == ';') continue;
        
        std::cout << name << " ";
        if (!std::getline(input, fact)) {
            return false;
        }

        // Add name,fact
        facts.insert(pair<string, string> (name, fact));
    }
    std::cout << std::endl;
    
    // Complete only if load facts
    return (facts.size() > 0);
}

