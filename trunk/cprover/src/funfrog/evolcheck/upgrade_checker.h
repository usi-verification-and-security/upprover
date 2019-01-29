/*******************************************************************

 Module: Upgrade checker using function summaries



\*******************************************************************/

#ifndef PROJECT_UPGRADE_CHECKER_H
#define PROJECT_UPGRADE_CHECKER_H

#include "funfrog/core_checker.h"

class upgrade_checkert
{
public:
	upgrade_checkert(
			const goto_programt &_goto_program,
			const goto_functionst &_goto_functions,
			const namespacet &_ns,
			const optionst& _options,
			ui_message_handlert &_message_handler,
			unsigned long &_max_memory_used )
	{};
	
};

//Declarations
bool check_initial(core_checkert &core_checker, messaget &msg);
bool check_upgrade(const goto_programt &program_old,
                   const goto_functionst &goto_functions_old,
                   const goto_programt &program_new,
                   const goto_functionst &goto_functions_new, const goto_modelt &new_model,
                   const optionst &options,
                   ui_message_handlert &message_handler);

#endif //PROJECT_UPGRADE_CHECKER_H
