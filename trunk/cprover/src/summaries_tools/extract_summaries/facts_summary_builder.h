/* 
 * File:   facts_summary_builder.h
 * Author: karinek
 *
 * Created on 31 August 2017, 10:33
 */

#ifndef FACTS_SUMMARY_BUILDER_H
#define FACTS_SUMMARY_BUILDER_H

#include <set>
#include "facts.h"

class facts_summary_buildert {
public:
    facts_summary_buildert(factst& f) : facts(f) {} 

    virtual ~facts_summary_buildert() {}
    
    void write_summary_facts(std::string file_name, std::set<std::string> headers);
    
private:
    factst& facts;
    
  
protected:
    /// Utilities
    string create_and_of_two_defs(string defa, string defb) {
        return " (and " + defa + " " + defb + ")";
    }
    string create_let_of_and_of_defs(string defa, string defb, string def_res) {
        return "(let ((" + def_res + " (and " + defa + " " + defb + ")))";
    }
    string create_let_of_facts(string fact, string def_res) {
        return "(let ((" + def_res + " " + fact + "))";
    }
    string create_next_def(int def_no) {
        return "?def" + std::to_string(def_no);
    }
};

#endif /* FACTS_SUMMARY_BUILDER_H */

