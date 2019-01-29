/*******************************************************************

 Module: Upgrade checker using function summaries.



\*******************************************************************/

#include "upgrade_checker.h"
#include "funfrog/check_claims.h"
#include "funfrog/assertion_info.h"
#include "diff.h"
#include "funfrog/utils/time_utils.h"
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

 Purpose: 2nd phase of upgrade checking;
\*******************************************************************/
bool check_upgrade(const goto_programt &program_old,
                   const goto_functionst &goto_functions_old,
                   const goto_programt &program_new,
                   const goto_functionst &goto_functions_new, const goto_modelt &new_model,
                   const optionst &options,
                   ui_message_handlert &message_handler) {
    
    auto before = timestamp();
    
    messaget msg(message_handler);
    
    //load __omega if it's already generated from 1st phase check_initial
    std::ifstream in;
    in.open(options.get_option("load-omega").c_str());
    
    if (in.fail()){
        std::cerr << "Failed to deserialize previous verification efforts (file: " <<
                  options.get_option("load-omega").c_str() <<
                  " cannot be read)" << std::endl;
        return 1;
    }
    
    difft diff(msg, options.get_option("load-omega").c_str(), options.get_option("save-omega").c_str() );
    
    bool res_diff = diff.do_diff(goto_functions_old, goto_functions_new);
    
    auto after = timestamp();
    msg.status() << "DIFF TIME: " << time_gap(after,before) << msg.eom;
    if (res_diff){
        msg.status() << "The program models are identical" <<msg.eom;
        return 0;
    }
    
    unsigned long max_mem_used;
    
    core_checkert core_checker(new_model, options, message_handler, max_mem_used);
    
    // Load older summaries (in the same way as hifrog)
    core_checker.initialize();
    
    symbol_tablet temp_symb;
    namespacet ns1 (temp_symb);
    
    upgrade_checkert upg_checker(program_new,
                                 goto_functions_new, ns1, options, message_handler, max_mem_used);
    
//    res_diff = upg_checker.check_upgrade();
    
    after = timestamp();
    
    msg.status() << "TOTAL UPGRADE CHECKING TIME: " << time_gap(after,before) << msg.eom;

//    upg_checker.save_change_impact();
    
    return res_diff;
}

