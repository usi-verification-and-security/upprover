#ifndef USER_DEFINED_SUMMARYT_H
#define USER_DEFINED_SUMMARYT_H

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>
#include "formula_manager.h"

class smtcheck_opensmt2t;
class optionst;

class UserDefinedSummaryt {
public:
    // FIXME: pass the decider here
    UserDefinedSummaryt() {}
    
    virtual ~UserDefinedSummaryt() {}
    
    void dump_list_templates(
            namespacet &ns, 
            const goto_programt &goto_program, 
            const goto_functionst &goto_functions,
            const optionst & options,
            unsigned int unwind,
            std::string logic,    
            const std::string& summary_file, ui_message_handlert & ui_message_handler);
    
private:    
    smtcheck_opensmt2t* decider;
};

#endif /* USER_DEFINED_SUMMARYT_H */

