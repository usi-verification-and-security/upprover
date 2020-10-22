/*******************************************************************

 Module: UpProver


\*******************************************************************/

#ifndef PROJECT_UPGRADE_CHECKER_H
#define PROJECT_UPGRADE_CHECKER_H

#include "funfrog/core_checker.h"
#include <ui_message.h>
#include <unordered_map>

class summary_validationt : public core_checkert
{
public:
	summary_validationt(
            const goto_modelt & _goto_model,
            //const goto_functionst &_goto_functions,
            //const namespacet &_ns,
            optionst & _options,
            ui_message_handlert & _message_handler,
            unsigned long & _max_memory_used
    )
			:
			core_checkert(
			    _goto_model,
				_options,
			    _message_handler,
				_max_memory_used)
	{};
    
    bool call_graph_traversal();
    void sanity_check(vector<call_tree_nodet*>& calls);
    
protected:
//counts total number of summary validation
    unsigned int counter_validation_check = 0;
//  for remembering the parents to be checked (upward refinement)
    std::unordered_set<call_tree_nodet*> marked_to_check;
    
    bool validate_node(call_tree_nodet & node);
	
	bool validate_summary(call_tree_nodet & node, summary_idt summary);
    void update_subtree_summaries(call_tree_nodet & node);
};

//Declarations
void check_initial(core_checkert &core_checker, messaget &msg);
bool launch_upprover(
        const goto_modelt &goto_model_old,
        const goto_modelt &goto_model_new,
        optionst &options,
        ui_message_handlert &message_handler);


#endif //PROJECT_UPGRADE_CHECKER_H
