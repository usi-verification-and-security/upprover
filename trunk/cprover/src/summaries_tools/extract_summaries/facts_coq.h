/* 
 * File:   facts_coq.h
 * Author: karinek
 *
 * Created on 31 August 2017, 10:32
 * 
 * TODO: need to upload files in Coq format into facts
 */

#ifndef FACTS_COQ_H
#define FACTS_COQ_H

#include "facts.h"

#include <string>
using namespace std;

class facts_coqt : public factst {
public:
    facts_coqt();

    virtual ~facts_coqt() {}
    
    virtual bool load_facts(std::string file_name);
    
    virtual std::string get_declare_original_function() { return ""; }  // TODO
    virtual std::string get_original_function_name() { return ""; } // TODO
    virtual std::string get_original_header_function() { return ""; } // TODO
    virtual bool is_return_value_unsigned() { return false; } // TODO
    virtual std::string get_params_set_of_function() { return ""; } // TODO
private:
    // TODO
};

#endif /* FACTS_COQ_H */

