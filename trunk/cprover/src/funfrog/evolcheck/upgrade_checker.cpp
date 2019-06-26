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
#include <langapi/language_util.h>

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
    
    upgrade_checkert upg_checker(goto_model_new, options, message_handler, max_mem_used);
    // Load older summaries (in the same way as hifrog)
    upg_checker.initialize();
    
    res_diff = upg_checker.check_upgrade();
    
    after = timestamp();
    
    msg.status() << "TOTAL UPGRADE CHECKING TIME: " << time_gap(after,before) << msg.eom;

//SA  upg_checker.save_change_impact();
    
    return res_diff;
}

/*******************************************************************\

Function: upgrade_checkert::check_upgrade

 Purpose: Incremental check of the upgraded program.

 // 3. Mark summaries as
//     - valid: the function was not changed                  => summary_info.preserved_node == true
//     - invalid: interface change                            [TBD], for now, all of them are 'unknown'
//                                / ass_in_subtree change     [TBD], suppose, every ass_in_subtree preserved
//     - unknown: function body changed                       => summary_info.preserved_node == false

//  3. From the bottom of the tree, reverify all changed nodes
//    a. If the edge is unchanged, check implication of previously used summaries
//        - OK/already valid: summary valid, don't propagate check upwards
//        - NO/already invalid: summary invalid, propagate check upwards
//    b. If the edge is changed, propagate check upwards (we don't know which summary
//       to check).
//
  //summaryt& summary = summary_store->find_summary(*it);
  //summary.print(std::cout);
\*******************************************************************/
bool upgrade_checkert::check_upgrade()
{
// Here we suppose that "__omega" already contains information about changes
// TODO: Maybe omega should be passed internally, not as a file.
    omega.deserialize(options.get_option("save-omega"),
            goto_model.goto_functions.function_map.at(goto_functionst::entry_point()).body); //double checke restore_call_info
    omega.process_goto_locations();
    omega.setup_last_assertion_loc(assertion_infot());
    
    std::vector<call_tree_nodet*>& calls = omega.get_call_summaries();
    
    //backward search, from the summary with the largest call location
    for (unsigned i = calls.size() - 1; i > 0; i--){
        bool is_verified = true;
        call_tree_nodet& current_node = *calls[i];
        std::string function_name = current_node.get_function_id().c_str();
        bool has_summary = summary_store->has_summaries(function_name);
//#ifdef DEBUG_UPGR
        std::cout << "checking summary #"<< i << ": " << function_name <<"\n";
//#endif
        const summary_ids_sett& used = (current_node).get_used_summaries();
        //if no summary used & not-preserved node -->upward
        if (!has_summary && !current_node.is_preserved_node()){
            is_verified = false;
            upward_traverse_call_tree((current_node).get_parent(), is_verified);
        }
        
        for (summary_ids_sett::const_iterator it = used.begin(); it != used.end(); ++it) {
            
            if (checked_summs.find(*it) == checked_summs.end()){
                summary_ids_sett summary_to_check;
                summary_to_check.insert(*it);
                (current_node).set_used_summaries(summary_to_check);
                upward_traverse_call_tree((current_node), is_verified);
            }
            else {
                status() << "function " << function_name << " is already checked" << eom;
            }
        }
        if (!is_verified) {
           //status() << "Invalid summaries ratio: " << omega.get_invalid_count() << "/" << (omega.get_call_summaries().size() - 1) << eom;
            report_failure();
            return false;
        }
    } //End of forloop
    
    //status() << "Invalid summaries ratio: " << omega.get_invalid_count() << "/"  << (omega.get_call_summaries().size() - 1) << eom;
    //update __omega file
    serialize();
    report_success();
    return true;
}

/*******************************************************************\

Function: upgrade_checkert::upward_traverse_call_tree


 Purpose: Traverses the function call stack to check the change,
          if the down-more attempt failed (pre == false)
          or from scratch (pre == true)

\*******************************************************************/
void upgrade_checkert::upward_traverse_call_tree(call_tree_nodet& node, bool& is_verified)   //pre -->is_verified
{
    status() << "checking validity of old summary for function: " << node.get_function_id() << eom;
    const summary_ids_sett& used = node.get_used_summaries();
    assert(used.size() <= 1); // we can check only one summary at a time
    if (used.empty()) { return; }
    
    //the accumulation of data from local node into global container
    for (summary_ids_sett::const_iterator it = used.begin(); it != used.end(); ++it){
        checked_summs.insert(*it);
    }
    
    //if the function has not changed, no need to check_summary;
    // we assume the previous summaries are sound and valid
    if (!node.is_preserved_node() || !is_verified) {
#ifdef DEBUG_UPGR
        if (!node.is_preserved_node()){
            std::cout << "  -- the body is changed;";
        }
#endif
        if (node.get_precision() == 1) { //Precision is "summary"
#ifdef DEBUG_UPGR
            if (node.get_precision() == 1){
                std::cout << " and there was a summary.\n";
            }
            else {
                std::cout << "   [parent check] do inlining.\n";
            }
#endif
            // prepare subst. scenario for reverification
            //TODO: then do the real check + refinement, if needed
            //in case of refinement, subst scenario will be renewed
            downward_traverse_call_tree (node);    // 1
    
            //real check; \phi_f => I_f.
            is_verified = check_summary(assertion_infot(), node, message_handler);
    
            if (is_verified){
                status() <<"  summary was verified. go to the next check." << eom; // here is the actual exit of the method
                node.set_summary();
            }
            else {
                summary_store->remove_summary(*used.begin());
                status() << "invalidating summary: " << node.get_function_id() << eom;
                node.clear_used_summaries();
                if (node.get_parent().is_root()){
                    status() <<"summary cannot be renewed. A real bug found. " <<eom;
                }
                else {
                    status() <<"check the parent." <<eom;
                    node.set_inline();
                    upward_traverse_call_tree(node.get_parent(), is_verified);
                }
            }
        }
        else {
            // no summary, but the code was changed. try checking the parent
            summary_store->remove_summary(*used.begin());
            node.set_inline();
            is_verified = false;
            upward_traverse_call_tree(node.get_parent(), is_verified);
        }
    }
    else {  //node is preserved
        status() <<"  preserved. go to the next check." <<eom;
    }
}

/*******************************************************************\

Function: upgrade_checkert::downward_traverse_call_tree

Purpose: Traverses the function call tree in order to re-configure
          subst. scenario for re-verifying a summary
\*******************************************************************/
void upgrade_checkert::downward_traverse_call_tree(call_tree_nodet& summary_info)
{
    call_sitest call_sites = summary_info.get_call_sites();
    for (call_sitest::iterator it = call_sites.begin();
         it != call_sites.end(); ++it)
    {
#ifdef DEBUG_UPGR
        status() << "\n    -- the function call of " << (it->second).get_function_id();
#endif
        if (it->second.is_preserved_edge()) {
#ifdef DEBUG_UPGR
            status() << " is preserved;";
#endif
            // FIXME: a summary that was being verified (both, valid or not) is INL now
            if ((it->second).get_precision() == 1){   //do nothing//will remain inlined
#ifdef DEBUG_UPGR
                status() << " has summary => will remain summarized ";
#endif
            }
            else if ((it->second).get_precision() == 0){  //do nothing//will remain inlined
#ifdef DEBUG_UPGR
                status() << " was havoced (probably, out of las_assertion_loc) => will remain havoced";
#endif
            }
            else { //means precision() == 2 --> inline     //traverse childs if any
                if ((it->second).has_assertion_in_subtree()){
#ifdef DEBUG_UPGR
                    status()<< " was inlined (since has assertion) => will remain inlined" ;
#endif
                    // if inline, then do recursive traverse downward
                    downward_traverse_call_tree(it->second);
                }
                else if ((it->second).is_preserved_node()){      //is preserved
#ifdef DEBUG_UPGR
                    status() << " was inlined (irrelevant for proof) => can be havoced";
#endif
                    (it->second).set_nondet();         //The only action of the method downward!    //WHY set_nondet() when preserved
                }
                else {      //has been changed and NO_assertion_in_subtree //will be inlined
#ifdef DEBUG_UPGR
                    status() << " was modified => should be inlined";
#endif
                }
            }
            
        }
        else {   //not preserved edge
#ifdef DEBUG_UPGR
            status() << " not preserved => do inlining";
#endif
        }
#ifdef DEBUG_UPGR
         << eom;
#endif
    }
}

/*******************************************************************\

Function: upgrade_checkert::check_summary

// NOTE: call check_summary to do the check \phi_f => I_f.

 Purpose: Checks whether an implementation of a function still implies
 its original summary.; implication  Phi_f --> If

\*******************************************************************/

bool upgrade_checkert::check_summary(const assertion_infot& assertion,
                                     call_tree_nodet& summary_info, ui_message_handlert &message_handler)
{
    auto before = timestamp();
    
    // Trivial case
    if(assertion.is_trivially_true())
    {
        status() <<"ASSERTION IS TRIVIALLY TRUE" <<eom;
        report_success();
        return true;
    }
    //const bool no_slicing_option = options.get_bool_option("no-slicing");
    
    std::vector<unsigned> ints;
    
    // so far, partial interpolation is disabled in the upgrade checking scenario
    
    partitioning_target_equationt equation(ns, *summary_store,
                                           true);
    //last flag store_summaries_with_assertion is initialized in all-claims/upgrade check with "true", otherwise normally false
    std::unique_ptr<path_storaget> worklist;
    symex_assertion_sumt symex{get_goto_functions(),
                               omega.get_call_tree_root(),
                               options, *worklist,
                               ns.get_symbol_table(),
                               equation,
                               message_handler,
                               get_main_function(),
                               omega.get_last_assertion_loc(),
                               omega.is_single_assertion_check(),
                               !options.get_bool_option("no-error-trace"),
                               options.get_unsigned_int_option("unwind"),
                               options.get_bool_option("partial-loops"),
    };
    symex.set_assertion_info_to_verify(&assertion);
    
    refiner_assertion_sumt refiner {
            *summary_store, omega,
            get_refine_mode(options.get_option("refine-mode")),
            message_handler, omega.get_last_assertion_loc()};//  //there was last flag for upgrade check as false
    
    bool assertion_holds = prepareSSA(symex);
    
    if (assertion_holds){
        // report results
        report_success();
        status() << ("This assertion trivially holds...\n") << eom;
        return true;
    }
    
    if(!assertion_holds && options.get_bool_option("claims-opt")){
        dependency_checkert(ns,
                            message_handler,
                            get_main_function(),
                            omega,
                            options.get_unsigned_int_option("claims-opt"),
                            equation.SSA_steps.size())
                .do_it(equation);
        status() << (std::string("Ignored SSA steps after dependency checker: ") + std::to_string(equation.count_ignored_SSA_steps())) << eom;
    }
    
    // the checker main loop:
    unsigned summaries_used = 0;
    unsigned iteration_counter = 0;
    prepare_formulat ssa_to_formula = prepare_formulat(equation, message_handler);
    
    auto solver = decider->get_solver();
    
    while (!assertion_holds)
    {
        iteration_counter++;
        
        //Converts SSA to SMT formula
        ssa_to_formula.convert_to_formula( *(decider->get_convertor()), *(decider->get_interpolating_solver()));
        
        // Decides the equation
        bool is_sat = ssa_to_formula.is_satisfiable(*solver);
        summaries_used = omega.get_summaries_count();
        
        assertion_holds = !is_sat;
        
        if (is_sat) {
            // this refiner can refine if we have summary or havoc representation of a function
            // Else quit the loop! (shall move into a function)
            if (omega.get_summaries_count() == 0 && omega.get_nondets_count() == 0)
                // nothing left to refine, cex is real -> break out of the refinement loop
                break;
            
            // Else, report and try to refine!
            
            // REPORT part
            if (summaries_used > 0){
                status() << "FUNCTION SUMMARIES (for " << summaries_used << " calls) AREN'T SUITABLE FOR CHECKING ASSERTION." << eom;
            }
            
            const unsigned int nondet_used = omega.get_nondets_count();
            if (nondet_used > 0){
                status() << "HAVOCING (of " << nondet_used << " calls) AREN'T SUITABLE FOR CHECKING ASSERTION." << eom;
            }
            // END of REPORT
            
            // figure out functions that can be refined
            refiner.mark_sum_for_refine(*solver, omega.get_call_tree_root(), equation);
            bool refined = !refiner.get_refined_functions().empty();
            if (!refined) {
                // nothing could be refined to rule out the cex, it is real -> break out of refinement loop
                break;
            } else {
                // REPORT
                status() << ("Go to next iteration\n") << eom;
                // do the actual refinement of ssa
                refineSSA(symex, refiner.get_refined_functions());
            }
        }
    } // end of refinement loop

    //////////////////
    // Report Part: //
    //////////////////
    
    // the assertion has been successfully verified if we have (end == true)
    const bool is_verified = assertion_holds;
    if (is_verified) {
        // produce and store the summaries
        if (!options.get_bool_option("no-itp")) {
#ifdef PRODUCE_PROOF
            if (decider->get_interpolating_solver()->can_interpolate()) {
                status() << ("Old summary is still valid...Start generating interpolants...") << eom;
                extract_interpolants(equation);
            } else {
                status() << ("Skip generating interpolants") << eom;
            }
#else
            assert(0); // Cannot produce proof in that case!
#endif
        
        } else {
            status() << ("Skip generating interpolants") << eom;
        } // End Report interpolation gen.
        
        // Report Summaries use
        if (summaries_used > 0)
        {
            status() << "FUNCTION SUMMARIES (for " << summaries_used
                     << " calls) WERE SUBSTITUTED SUCCESSFULLY." << eom;
        } else {
            status() << ("ASSERTION(S) HOLD(S) WITH FULL INLINE") << eom;
        }
        
        // report results
        report_success();
        
    } // End of UNSAT section
    else // assertion was falsified
    {
        assertion_violated(ssa_to_formula, symex.guard_expln);
    }
    // FINAL REPORT
    
    auto after = timestamp();
    omega.get_unwinding_depth();
    
    status() << "Initial unwinding bound: " << options.get_unsigned_int_option("unwind") << eom;
    status() << "Total number of steps: " << iteration_counter << eom;
    if (omega.get_recursive_total() > 0){
        status() << "Unwinding depth: " <<  omega.get_recursive_max() << " (" << omega.get_recursive_total() << ")" << eom;
    }
    status() << "TOTAL TIME FOR CHECKING THIS CLAIM: " << time_gap(after,before) << eom;

#ifdef PRODUCE_PROOF
    if (assertion.is_single_assert()) // If Any or Multi cannot use get_location())
        status() << ((assertion.is_assert_grouping())
                     ? "\n\nMain Checked Assertion: " : "\n\nChecked Assertion: ") <<
                 "\n  file " << assertion.get_location()->source_location.get_file() <<
                 " line " << assertion.get_location()->source_location.get_line() <<
                 " function " << assertion.get_location()->source_location.get_function() <<
                 "\n  " << ((assertion.get_location()->is_assert()) ? "assertion" : "code") <<
                 "\n  " << from_expr(ns, "", assertion.get_location()->guard)
                 << eom;
#endif
    
    return is_verified;
}