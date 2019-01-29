/*******************************************************************

 Module: Upgrade checker using function summaries.



\*******************************************************************/

#include "upgrade_checker.h"
#include "funfrog/check_claims.h"
#include "funfrog/assertion_info.h"

/*******************************************************************\

Standalone Function: check_initial

  Inputs:

 Outputs:

 Purpose: Check the whole system and prepare for incremental
 check of upgrades via check_upgrade.
\*******************************************************************/
bool check_initial(core_checkert &core_checker, messaget &msg) {

  // Check all the assertions  ; the flag is true because of all-claims
	bool result = core_checker.assertion_holds(assertion_infot(), true);

  	if (result) {
    	msg.status() << "\n Initial phase for Upgrade checking is successfully done, \n"
                    " Now proceed with \"do-upgrade-check\" of the upgraded code! Enjoy Verifying!\n" << msg.eom;
 	}
  	else {
    	msg.status() << "\n Upgrade checking is not possible!" << msg.eom;
    	msg.status() << "Try standalone verification" << msg.eom;
  	}
    //to write the substitution scenario of 1st phase into a given file or __omega file
    core_checker.serialize();
  	
  	return result;    //you better move the report msgs to the caller place
}

/*******************************************************************\
 Function: check_upgrade

 Inputs:

 Outputs:

 Purpose:
\*******************************************************************/
bool check_upgrade(const goto_programt &program_old,
				   const goto_functionst &goto_functions_old,
				   const goto_programt &program_new,
				   const goto_functionst &goto_functions_new,
				   const optionst& options,
				   ui_message_handlert &message_handler) {
  
  
	return true;
}