/*******************************************************************\

Module: Storage class for function summaries (union-find).

Author: Ondrej Sery

\*******************************************************************/
#include "smt_z3_summary_store.h"

#include <sstream>
#include <fstream>

#include "solvers/smt_itp.h"
#include "solvers/smtcheck_opensmt2.h"
#include "solvers/smtcheck_z3.h"
#include "solvers/smt_itp_z3.h"
#include "utils/naming_helpers.h"

// Serialization SMT
void smt_z3_summary_storet::serialize(std::ostream &out) const {;
    for (const auto & summary_node : store){
        if(summary_node.is_repr()){
            summary_node.summary->serialize(out);
        }
    }
}

// Basic parsing of the input file into functions
// TODO: move to utils
std::vector<std::string> smt_z3_summary_storet::get_functions(std::string file_name)
{
    assert(file_name.size() > 0);
    
    std::ifstream sumfile(file_name);
    
    std::vector<std::string> functions;
    std::string line;
    std::string curr="";
    while (std::getline(sumfile, line))
    {
        if (line.find("(define-fun ") != std::string::npos) {
            if (curr.size() > 0) functions.push_back(curr);
            curr = line; 
        } else {
            curr += line;
        }
    }
    // push the last one!
    if (curr.size() > 0) {
        functions.push_back(curr);
    }
    
    return functions;
}

// SMT logics deser
void smt_z3_summary_storet::deserialize(std::vector<std::string> fileNames) {
    this->clear();

    for (const auto & fileName : fileNames) {
        try {
            // Read as string from the current file
            std::vector<std::string> functions = get_functions(fileName);
            for (unsigned i = 0; i < functions.size(); ++i) {
                smt_itp_z3t* itp = new smt_summary_z3t();
                
                // Name of the function - TODO move to utils
                std::size_t start_pos = functions[i].find("(define-fun ")+12;
                std::size_t end_pos = functions[i].find("(", start_pos);
                std::string fname = functions[i].substr(start_pos, end_pos-start_pos-1);
                
                // split header from body
                assert(functions[i].find(") Bool ") != std::string::npos); // shall have the header end
                std::size_t split_pos = functions[i].find(") Bool ")+7;
                std::string header = functions[i].substr(end_pos, split_pos-1-end_pos);
                std::string body = functions[i].substr(split_pos, functions[i].size()-1-split_pos);

                // adds the function with its fabricated assert (z3 constraints.... as it is pure solver)
                itp->setTterm(functions[i]);
                itp->setArgs(header);
                
                clean_name(fname); // + remove space!
                itp->setInterpolant(body);
                this->insert_summary(itp, fname);  //ret val not used?!
            }
        } catch (...) { // default, TODO: map the errors
            std::cerr << "Non linear operation encounter in file " << fileName << ". Ignoring this file.\n";
        }
    }
}

/*******************************************************************\

Function: summary_storet::insert_summary

  Inputs:

 Outputs:

 Purpose: Removed most of the code as we don't save template in z3
 * thus no need for new names for each function version

\*******************************************************************/

void smt_z3_summary_storet::insert_summary(summaryt *summary, const std::string & function_name) {
    smt_summary_z3t * smt_summary = dynamic_cast<smt_summary_z3t*>(summary);
    if(!smt_summary){
        std::cerr << "Ignoring insertion of a summary into the summary store, not compatible type\n";
        return;
    }

    assert(!is_quoted(function_name));
    assert(!fun_name_contains_counter(function_name));

    // call the base functionality
    summary_storet::insert_summary(summary, function_name);
}