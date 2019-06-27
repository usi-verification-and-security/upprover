/*******************************************************************

 Module: Upgrade checker using function summaries



\*******************************************************************/

#ifndef PROJECT_UPGRADE_CHECKER_H
#define PROJECT_UPGRADE_CHECKER_H

#include "funfrog/core_checker.h"
#include <ui_message.h>

class upgrade_checkert : public core_checkert
{
public:
	upgrade_checkert(
			const goto_modelt & _goto_model,
			//const goto_functionst &_goto_functions,
			//const namespacet &_ns,
			const optionst& _options,
			ui_message_handlert &_message_handler,
			unsigned long &_max_memory_used
			)
			:
			core_checkert(
			    _goto_model,
				_options,
			    _message_handler,
				_max_memory_used)
	{};
    
    bool check_upgrade();
    bool check_summary(const assertion_infot& assertion,
                       call_tree_nodet& summary_info, ui_message_handlert &message_handler);

protected:
    summary_ids_sett checked_summs;
	void upward_traverse_call_tree(call_tree_nodet& summary_info, bool &is_verified);
	void downward_traverse_call_tree(call_tree_nodet& summary_info);
	
	bool validate_node(call_tree_nodet & node, bool force_check);
	
	bool validate_summary(call_tree_nodet & node, summary_idt summary);
};

//Declarations
bool check_initial(core_checkert &core_checker, messaget &msg);
bool check_upgrade(
		const goto_modelt &goto_model_old,
		const goto_modelt &goto_model_new,
		const optionst &options,
		ui_message_handlert &message_handler);


#endif //PROJECT_UPGRADE_CHECKER_H
