/*******************************************************************

 Module: Upgrade checker using function summaries



\*******************************************************************/

#ifndef PROJECT_UPGRADE_CHECKER_H
#define PROJECT_UPGRADE_CHECKER_H

#include "funfrog/core_checker.h"
#include <ui_message.h>
#include <unordered_map>

class upgrade_checkert : public core_checkert
{
public:
	upgrade_checkert(
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
    
    bool check_upgrade();
    void sanity_check(vector<call_tree_nodet*>& calls);


//    // Removes summary from the summary store
//    void remove_summary(call_tree_nodet * node, summary_idt to_delete){
//        callNode_to_summaryIds.at(node).erase(to_delete);
//    }
//
//    const summary_ids_sett& get_set_SummaryIds(call_tree_nodet * node) const{
//        return callNode_to_summaryIds.at(node);
//    }
//
//    void update_SummaryIds(call_tree_nodet * node, summary_idt& new_id){
//        callNode_to_summaryIds.at(node).insert(new_id);
//    }
    
protected:
//    std::unordered_map<call_tree_nodet*, summary_ids_sett> callNode_to_summaryIds;
//
//    summary_ids_sett checked_summs;
	
	bool validate_node(call_tree_nodet & node);
	
	bool validate_summary(call_tree_nodet & node, summary_idt summary);
    void update_subtree_summaries(call_tree_nodet & node);
};

//Declarations
void check_initial(core_checkert &core_checker, messaget &msg);
bool do_upgrade_check(
        const goto_modelt &goto_model_old,
        const goto_modelt &goto_model_new,
        optionst &options,
        ui_message_handlert &message_handler);


#endif //PROJECT_UPGRADE_CHECKER_H
