#ifndef USER_DEFINED_SUMMARYT_H
#define USER_DEFINED_SUMMARYT_H

#include "prepare_smt_formula.h"
#include "summarization_context.h"

class check_opensmt2t;

class UserDefinedSummaryt {
public:
    // FIXME: pass the decider here
    UserDefinedSummaryt() {}
    
    virtual ~UserDefinedSummaryt() {}
    
    void dump_list_templates(
            namespacet &ns, 
            const goto_programt &goto_program, 
            const goto_functionst &goto_functions,
            unsigned int unwind,
            std::string logic,    
            const std::string& summary_file);
    
private:    
    check_opensmt2t* decider;
};

#endif /* USER_DEFINED_SUMMARYT_H */

