/*******************************************************************

 Module: Upgrade checker using function summaries.



\*******************************************************************/

#include <funfrog/partitioning_target_equation.h>    //check if is OK
#include <goto-symex/path_storage.h>         //
#include <funfrog/symex_assertion_sum.h>    //
#include <funfrog/refiner_assertion_sum.h>
#include <funfrog/dependency_checker.h>
#include <funfrog/prepare_formula.h>
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
                    " Now proceed with \"do-upgrade-check\" for verifying the new version of your code! Enjoy Verifying!\n" << msg.eom;
 	}
  	else {
    	msg.status() << "\n Upgrade checking is not possible!" << msg.eom;
    	msg.status() << "Try standalone verification" << msg.eom;
  	}
    //to write the substitution scenario of 1st phase into a given file or __omega file
    msg.status() << "Writing the substitution scenarios into a given file or __omega file" << msg.eom;
  	core_checker.serialize();
  	
  	return result;
}
/*******************************************************************\
 Function: check_upgrade

 Purpose: 2nd phase of upgrade checking;
\*******************************************************************/
/*
void upgrade_checkert::initialize()
{
    // Prepare the summarization context
    summarization_context.analyze_functions(ns);  //call the ctor of symex_assertion_sumt, it will call internally analyze_globals();
                                                    //which is equivalent to this analyze_functions()
    
    // Load older summaries
    {
        const std::string& summary_file = options.get_option("load-summaries");
        if (!summary_file.empty()) {
            summarization_context.deserialize_infos(summary_file);  //in new hifrog: summary_store->deserialize ;
            // dont wory about deserilzation; assume it is correct!
        }
    }
}
*/
/*******************************************************************\
 Function: check_upgrade

 Purpose: 2nd phase of upgrade checking;
\*******************************************************************/
bool check_upgrade(
        // goto_program and goto_functions can be obtained from goto_model; so only get goto_model
        //const goto_programt &program_old,
        //const goto_functionst &goto_functions_old,
        const goto_modelt &goto_model_old,
        //const goto_programt &program_new,
        // const goto_functionst &goto_functions_new,
        const goto_modelt &goto_model_new,
        const optionst &options,
        ui_message_handlert &message_handler)
{
    
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
    
    bool res_diff = diff.do_diff(goto_model_old.goto_functions, goto_model_new.goto_functions);  //if result is false it mean at least one of the functions has changed
    
    auto after = timestamp();
    msg.status() << "DIFF TIME: " << time_gap(after,before) << msg.eom;
    if (res_diff){
        msg.status() << "The program models are identical" <<msg.eom;
        return 0;
    }
    
    unsigned long max_mem_used;
    
    
    // Load older summaries (in the same way as hifrog)
    
    /*symbol_tablet temp_symb;   //SA:do we need to define a new namespace?
    namespacet ns1 (temp_symb);*/
    
    upgrade_checkert upg_checker(goto_model_new, options, message_handler, max_mem_used);
    upg_checker.initialize();
    
    res_diff = upg_checker.check_upgrade();    //before here omega lost repetitive items(re-written). where?
    
    after = timestamp();
    
    msg.status() << "TOTAL UPGRADE CHECKING TIME: " << time_gap(after,before) << msg.eom;

//SA  upg_checker.save_change_impact();
    
    return res_diff;
}

/*******************************************************************\

Function: upgrade_checkert::check_upgrade

 Purpose: Incremental check of the upgraded program.

\*******************************************************************/
bool upgrade_checkert::check_upgrade()
{
    
    // Here we suppose that "__omega" already contains information about changes
    // TODO: Maybe omega should be passed internally, not as a file.
    omega.deserialize(options.get_option("save-omega"),
            goto_model.goto_functions.function_map.at(goto_functionst::entry_point()).body);  //SA: fix the bug in restore_call_info
    omega.process_goto_locations();
    omega.setup_last_assertion_loc(assertion_infot());
    
    // 3. Mark summaries as
    //     - valid: the function was not changed                  => summary_info.preserved_node == true
    //     - invalid: interface change                            [TBD], for now, all of them are 'unknown'
    //                                / ass_in_subtree change     [TBD], suppose, every ass_in_subtree preserved
    //     - unknown: function body changed                       => summary_info.preserved_node == false
    
    std::vector<call_tree_nodet*>& summs = omega.get_call_summaries();
    for (unsigned i = summs.size() - 1; i > 0; i--){
        // backward search, from the summary with the largest call location
        
        bool res = true;
        
        const irep_idt& name = (*summs[i]).get_function_id();

//SA #ifdef DEBUG_UPGR
        std::cout << "checking summary #"<< i << ": " << name <<"\n";
//#endif
        // if (omega.get_last_assertion_loc() >= (*summs[i]).get_call_location()){
        
        const summary_ids_sett& used = (*summs[i]).get_used_summaries();
        if (used.size() == 0 && !(*summs[i]).is_preserved_node()){
            res = false;
//SA           upward_traverse_call_tree((*summs[i]).get_parent(), res);
        }
        
        for (summary_ids_sett::const_iterator it = used.begin(); it != used.end(); ++it) {
//        summaryt& summary = summarization_context.get_summary_store().find_summary(*it);
//        summary.print(std::cout);
            
            if (checked_summaries.find(*it) == checked_summaries.end()){
                summary_ids_sett summary_to_check;
                summary_to_check.insert(*it);
                (*summs[i]).set_used_summaries(summary_to_check);
///SA                upward_traverse_call_tree((*summs[i]), res);
            } else {
                status() << "function " << name << " is already checked" << eom;
            }
        }
        /* } else {
             status(std::string("ignoring function: ") + name.c_str()
                 + std::string(" (loc. number ") + i2string((*summs[i]).get_call_location())
                 + std::string(" is out of assertion scope)"));
         }*/
        if (!res) {
///SA            status() << "Invalid summaries ratio: " << omega.get_invalid_count() << "/" << (omega.get_call_summaries().size() - 1) << eom;
            report_failure();
            return false;
        }
    }
    
    // 3. From the bottom of the tree, reverify all changed nodes
    //    a. If the edge is unchanged, check implication of previously
    //       used summaries
    //        - OK/already valid: summary valid, don't propagate check upwards
    //        - KO/already invalid: summary invalid, propagate check upwards
    //    b. If the edge is changed, propagate check upwards (we don't know which summary
    //       to check).
    //
    // NOTE: call check_summary to do the check \phi_f => I_f.
    
///SA    status() << "Invalid summaries ratio: " << omega.get_invalid_count() << "/"  << (omega.get_call_summaries().size() - 1) << eom;
    serialize();
    report_success();
    return true;
}
