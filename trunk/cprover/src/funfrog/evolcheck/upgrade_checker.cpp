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
  	return result;
}