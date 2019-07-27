/*******************************************************************

 Module: Upgrade checking using function summaries.



\*******************************************************************/

#include <funfrog/partitioning_target_equation.h>
#include <goto-symex/path_storage.h>
#include <funfrog/symex_assertion_sum.h>
#include <funfrog/refiner_assertion_sum.h>
#include <funfrog/dependency_checker.h>
#include <funfrog/prepare_formula.h>
#include "upgrade_checker.h"
#include "funfrog/check_claims.h"
#include "funfrog/assertion_info.h"
#include "diff.h"
#include "funfrog/utils/time_utils.h"
#include <langapi/language_util.h>
#include "funfrog/partition_iface.h"
#include <funfrog/solvers/smt_itp.h>
#include <funfrog/utils/SummaryInvalidException.h>
/*******************************************************************\

Standalone Function: check_initial phase of upgrade check (bootstraping)


 Purpose: Check the whole system and prepare for incremental
 check of upgrades via check_upgrade.
\*******************************************************************/
void check_initial(core_checkert &core_checker, messaget &msg) {

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
}

/*******************************************************************\
 Function: do_upgrade_check

 Purpose: 2nd phase of upgrade checking; triggers upgrade checking
\*******************************************************************/
bool do_upgrade_check(
        // goto_program and goto_functions can be obtained from goto_model; so only get goto_model
        //const goto_programt &program_old,
        //const goto_functionst &goto_functions_old,
        const goto_modelt &goto_model_old,
        //const goto_programt &program_new,
        // const goto_functionst &goto_functions_new,
        const goto_modelt &goto_model_new,
        optionst &options,
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

    // init solver and Load older summaries in the same as hifrog
    init_solver_and_summary_store();
    
    std::vector<call_tree_nodet*>& calls = omega.get_call_summaries();
    
    //iterate over functions backward, from node with the largest call location
    for (unsigned i = calls.size() - 1; i > 0; i--){
        call_tree_nodet& current_node = *calls[i];
        std::string function_name = current_node.get_function_id().c_str();

        bool validated = validate_node(current_node, false);
        if (validated) {
            status() << "Node " << function_name << " has been validated" << eom;
        }
        else {
            status() << "Validation failed! A real bug found. " << eom;
            report_failure();
            return false;
        }
    } //End of forloop
    
    //update __omega file
    serialize();
    
    report_success();
    return true;
}

/*******************************************************************\

Function:

Purpose: it starts bottom up, checking nodes validity one by one in the new
upgraded version; we assume each node potentially has at most one summary.
\*******************************************************************/
bool upgrade_checkert::validate_node(call_tree_nodet &node, bool force_check) {
    
    const std::string function_name = node.get_function_id().c_str();
    bool check_necessary = !node.is_preserved_node() || force_check;
    bool validated = !check_necessary;

    if (check_necessary) {
        bool has_summary;
        has_summary = summary_store->has_summaries(function_name);
        //TODO get summaries based on call-nodes, not function name(as different nodes can have different summary)
        if (has_summary){
            //we only take one summary per node
            const summary_idt &single_sum = summary_store->get_summariesID(function_name)[0];
            validated = validate_summary(node , single_sum);
            if (!validated) {
                // TODO: invalidate summary for call tree node -> remove summary_id and set precision
                //                                             -> delete summary from summary store
                //node.remove_summary(single_sum);
                //summary_store->remove_summary(single_sum);
                
            }
        }
        if (!validated) {
            bool has_parent = (!node.is_root()) && (node.get_function_id()!=ID_main);
            if (has_parent) {
                validated = validate_node(node.get_parent(), true);
            }
            else { // Final check: we are in the main, and we dont have a summary form previous run
                // DO a classic HiFrog check and normal refinement (inline if summary not enough) if
                // it reaches the top-level main and fails --> report immediately
                // Check all the assertions  ; the last flag is true because of all-claims
                validated = this->assertion_holds(assertion_infot(), true);
            }
            if(validated) {
                // TODO: make sure that call_tree_nodes have the correct information about summaries
                //update summaries for subtrees(add new summary, or replace their old summaries)
            }
        }
    }

    return validated;
}
/*******************************************************************\

Function: upgrade_checkert::validate_summary

// NOTE: checks implication \phi_f => I_f.

 Purpose: Checks whether a new implementation of a function still implies
 its original summary?

\*******************************************************************/

bool upgrade_checkert::validate_summary(call_tree_nodet &node, summary_idt summary_id) {

    partitioning_target_equationt equation(ns, *summary_store, true);
    //last flag store_summaries_with_assertion is initialized in all-claims/upgrade check with "true", otherwise normally false

    std::unique_ptr<path_storaget> worklist;
    symex_assertion_sumt symex{get_goto_functions(),
                               node,
                               options, *worklist,
                               ns.get_symbol_table(),
                               equation,
                               message_handler,
                               get_goto_functions().function_map.at(node.get_function_id()).body,
                               omega.get_last_assertion_loc(),
                               omega.is_single_assertion_check(),
                               !options.get_bool_option("no-error-trace"),
                               options.get_unsigned_int_option("unwind"),
                               options.get_bool_option("partial-loops"),
    };
    assertion_infot assertion_info;
    symex.set_assertion_info_to_verify(&assertion_info);

    refiner_assertion_sumt refiner {
            *summary_store, omega,
            get_refine_mode(options.get_option("refine-mode")),
            message_handler, omega.get_last_assertion_loc()};//  //there was last flag for upgrade check as false

    bool assertion_holds = prepareSSA(symex);

    if (assertion_holds){
        report_success();
        return true;
    }

    // the checker main loop:
    unsigned summaries_used = 0;
    unsigned iteration_counter = 0;
    prepare_formulat ssa_to_formula = prepare_formulat(equation, message_handler);

    //local creation of solver; in every call a fresh raw pointer to solver is created.
    auto solver = decider->get_solver();
    // first partition for the summary to check
    auto interpolator = decider->get_interpolating_solver();
    //refers to entry partition including its subtree
    auto& entry_partition = equation.get_partitions()[0];
    fle_part_idt summary_partition_id = interpolator->new_partition();
    (void)(summary_partition_id);
    // TODO split, we need to negate first!
    itpt& summary = summary_store->find_summary(summary_id);
    // TODO: figure out a way to check beforehand whether interface matches or not
    try {
        interpolator->substitute_negate_insert(summary, entry_partition.get_iface().get_iface_symbols());
    }
    catch (SummaryInvalidException& ex) {
        // Summary cannot be used for current body -> invalidated
        return false;
    }
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

    // the assertion has been successfully verified if we have (end == true)
    const bool is_verified = assertion_holds;
    if (is_verified) {
        // produce and store the summaries
        assert(decider->get_interpolating_solver()->can_interpolate());
        extract_interpolants(equation);
    } // End of UNSAT section
    else // assertion was falsified
    {
        assertion_violated(ssa_to_formula, symex.guard_expln);
    }

    return is_verified;
}

/*******************************************************************\

Function:

Purpose:
\*******************************************************************/
/*void upgrade_checkert::update_subtree_summaries(call_tree_nodet &node) {
    //if the child did not have summary, add newly generated sum
    //if the child had sumary, remove its summary, and replace it with newly generated sum
    status() << "Not implemented yet!" <<eom;
}*/

