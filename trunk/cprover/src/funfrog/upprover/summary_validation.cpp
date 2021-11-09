/*******************************************************************

 Module: UpProver: Incremental verification of changes using function summaries.

\*******************************************************************/
#include <funfrog/partitioning_target_equation.h>
#include <goto-symex/path_storage.h>
#include <funfrog/symex_assertion_sum.h>
#include <funfrog/refiner_assertion_sum.h>
#include <funfrog/formula_manager.h>
#include "summary_validation.h"
#include "funfrog/check_claims.h"
#include "funfrog/assertion_info.h"
#include "diff.h"
#include "funfrog/utils/time_utils.h"
#include <langapi/language_util.h>
#include "funfrog/partition_iface.h"
#include <funfrog/solvers/smt_itp.h>
#include <funfrog/utils/SummaryInvalidException.h>
#include <unordered_set>

#define HOUDINI_REF
#define DEBUG_HOUDINI
/*******************************************************************\

Standalone Function: check_initial

Purpose: initial phase of upprover (bootstraping)
\*******************************************************************/
void check_initial(core_checkert &core_checker, messaget &msg) {

  // Check all the assertions  ; the flag is true because of all-claims
	bool result = core_checker.assertion_holds(assertion_infot(), true);

  	if (result) {
        msg.status() << "\n Bootstrapping phase is successful, \n"
        " Now proceed with option \"--summary-validation\" for verifying the new version of your code!\n" << msg.eom;
        
    	msg.status() << "Writing the substitution scenarios into a given file or __omega file" << msg.eom;
        core_checker.serialize();
 	}
  	else {
    	msg.status() << "\n Incremental verification is not possible due to absence of summaries!" << msg.eom;
    	msg.status() << "Try standalone verification" << msg.eom;
  	}

}
/*******************************************************************\
 Function: launch_upprover

 Purpose: 2nd phase of UpProver
 Note: goto_program and goto_functions can be obtained from goto_model; so only get goto_model
 no need for goto_programt and const goto_functionst
\*******************************************************************/
bool launch_upprover(
        const goto_modelt &goto_model_old,
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
    bool res_diff = diff.do_diff(goto_model_old, goto_model_new); //false means at least one function has changed
    auto after = timestamp();
    msg.status() << "DIFF TIME: " << time_gap(after,before) << msg.eom;
    if (res_diff){
        msg.status() << "The program models are identical" <<msg.eom;
        if(!options.is_set("TIP-check")){
            return 0;
        }
    }
    unsigned long max_mem_used;
    summary_validationt upg_checker(goto_model_new, options, message_handler, max_mem_used);
    //main functionality
    res_diff = upg_checker.call_graph_traversal();
    after = timestamp();
    msg.status() << "TOTAL SUMMARY VALIDATION TIME: " << time_gap(after,before) << msg.eom;
//SA  upg_checker.save_change_impact();
    
    return res_diff;
}

/*******************************************************************\
 Purpose: Incremental check of the changed program.

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
  //itpt_summaryt& summary = summary_store->find_summary(*it);
  //summary.print(std::cout);
\*******************************************************************/
/*******************************************************************\
 Function: call_graph_traversal

 Purpose: It starts bottom up over the changed lists, invokes validation_node() if necessary;
 we assume each node potentially has at most one summary.
 Note:
 Iterates over the function calls, bottom up, and propagates towards the parents.
 First children (and their siblings) will be checked and parents will be marked
 for later check.
 If the individual node:
 Not changed & Not force-check ==> do nothing, go to next node
 changed||force-check ==> validite_node (if has summary->validate_summary)
\*******************************************************************/
bool summary_validationt::call_graph_traversal()
{
    // we suppose "__omega" already contains information about changes
    //extract info from omega file(e.g., function ID, summary ID, call location, preserved,....) to several call-tree-nodet(call_site)
    omega.deserialize(options.get_option("save-omega"),
            goto_model.goto_functions.function_map.at(goto_functionst::entry_point()).body); //double check restore_call_info
    omega.process_goto_locations();
    omega.setup_last_assertion_loc(assertion_infot());
    // init solver and load older summaries in the same way as hifrog
    init_solver_and_summary_store();
    
    std::vector<call_tree_nodet*>& calls = omega.get_call_summaries();
    if(options.is_set("TIP-check")){
      TIP_sanity_check(calls);
    }
    bool validated = false;
//    auto before_iteration_over_functions = timestamp();
    //iterate over functions in reverse order of Pre-order traversal, from node with the largest call location
    for (unsigned i = calls.size() - 1; i > 0; i--){
        call_tree_nodet& current_node = *calls[i];
        std::string function_name = current_node.get_function_id().c_str();
        bool force_check = false;
        if (marked_to_check.find(&current_node) != marked_to_check.end()){
            force_check = true;
        }
        bool check_necessary = !current_node.is_preserved_node() || force_check;
        if(!check_necessary) continue;
        validated = !check_necessary;
        if (check_necessary){
            validated = validate_node(current_node);
        }
        if (!validated) {
            bool has_parent = current_node.get_function_id()!=ID_main;
            if (has_parent) {
                marked_to_check.insert(&current_node.get_parent());
            }
            if(current_node.get_function_id() == ID_main){
                // Final check:  main function
                status() << "------Final validation node " << function_name << " ..." << eom;
                counter_validation_check++;
//                check_opensmt2t* solver = dynamic_cast<check_opensmt2t*>(decider->get_solver());
                //size_t main_args_size = goto_model.goto_functions.function_map.at(current_node.get_function_id()).parameter_identifiers.size();
                // create a false summary for main function to obtain just ID, although won't be used.
                //itpt * summary_main = solver->create_false_summary(function_name);
                //summary_idt sumID_main = summary_store->insert_summary(summary_main, function_name);
                //validated = validate_summary(current_node, sumID_main);
                decider->get_solver()->reset_solver();
                //classic HiFrog check
                validated = this->assertion_holds_smt(assertion_infot(), true);
            }
        }
        if (validated){
            status() << "------Node " << function_name << " has been validated!" << eom;
        }
        else {
            status() << "------Node " << function_name << " was NOT validated!" << eom;
        }
    } //End of forloop
//    auto after_iteration_over_functions  = timestamp();
//    status() << "\nTotal iteration TIME over ALL functions for node validation (includes sub-SYMEX+CONVERSION+SOLVING times): "
//             << time_gap(after_iteration_over_functions,before_iteration_over_functions) << eom;
    //Final conclusion
    if (validated) {
        status() << "\nValidation Done!" << eom;
    }
    else {
        status() << "Validation failed! A real bug found. " << eom;
        report_failure();
        status() << "\n### Total number of validation check (implication check via solver): " << counter_validation_check << eom;
        status() << "### Total number of deleted summary IDs: " << summary_store->deleted_sumIDs.size() << eom;
        status() << "### Total number of generated summaries: " << summary_store->generated_sumIDs.size() << eom;
        status() << "### Total number of repaired summaries: " << repaired_nodes.size() <<"\n" << eom;
    
        return false;
    }
    //update __omega file
    serialize();
    //update summary file for subsequent runs
    summary_store->serialize(options.get_option(HiFrogOptions::SAVE_FILE));
    report_success();
    status() << "\n### Total number of validation check (implication check via solver): " << counter_validation_check << eom;
    status() << "### Total number of deleted summaries: " << summary_store->deleted_sumIDs.size() << eom;
    status() << "### Total number of generated summaries: " << summary_store->generated_sumIDs.size()  << eom;
    status() << "### Total number of repaired summaries: " << repaired_nodes.size() <<"\n" << eom;
    return true;
}

/*******************************************************************\
Function:

Purpose: Triggers validation of summary associated with the node
Note: Obtain summaries based on call-nodes, not function name(as different nodes can have different summaries)
// hack to update the summaryFile for the next occasion(for e.g, we will need the updated summaries
// for the next decider which will read this summaryFile to update the summary_storet)
 NOTE: summary of each function has single ID and single PTref stored in Logic
NOTE: When summary vas invalid:
//if is'nt conjunctive, invalidate summary for call tree node, i.e., remove summary_id, delete summary itself from summary store,
and set precision
//if it's conjunctive, drop one conjunct per time: add the resultant summary to summary_storet and ask for new ID
NOTE: Remember to delete from 4 places: vec: store, map:function_to_summary, map:id_to_summary, set:summary_IDset
N.B: no-need for wrapper: std::shared_ptr<summary_storet> summary_store_backup = this->summary_store;
\*******************************************************************/
bool summary_validationt::validate_node(call_tree_nodet &node) {
    
    const std::string function_name = node.get_function_id().c_str();
    bool validated = false;
    status() << "\n------validating node " << function_name << " ..." << eom;
    bool has_summary;
    //has_summary = summary_store->has_summaries(function_name); //no! when there are several same-name-nodes, cannot distinguish the summaries per node. use the next line
    has_summary = node.get_node_sumID() != 0; //yes, summary associated with node; zero initial value
    //TODO when this node has not summary, but its homonyms has summaries, find a way to use it soundly
    if (!has_summary) {
        status() << "------there is no summary ID for this node in omega!" << eom;
    }
    else {
        //there is only one summary per node due to full unrolling using goto-instrument
//      const summary_idt single_sumID2 = summary_store->get_summariesID(function_name)[0];//don't do this as it always take the same ID for all
        //const summary_idt sumID_full = *(node.get_used_summaries().begin());
        const summary_idt sumID_full = node.get_node_sumID();
        //TODO if the summary is true dont call method validate_summary(), it's gonna be captured anyway
//      print summary-in-use in the console
//      itpt_summaryt& currentSum = summary_store->find_summary(single_sumID);
//      currentSum.serialize(std::cout);
  
        itpt_summaryt &itpFull = summary_store->find_summary(sumID_full);
        smt_itpt_summaryt *sumFull = dynamic_cast<smt_itpt_summaryt *>(&itpFull);
        PTRef sumFull_pref = sumFull->getInterpolant();
        // auto decider_backup = this->decider;  //shared_ptr 2nd wrapper for object to keep it alive for next itter
        smtcheck_opensmt2t *solver = dynamic_cast<smtcheck_opensmt2t *>(decider->get_solver());
        assert(solver);
      
        validated = validate_summary(node , sumID_full, solver->isConjunctive(sumFull_pref));
        if (!validated) {
            //Since the original summary of node was invalid, mark the parent to be checked anyway
            bool has_parent = node.get_function_id() != ID_main;
            if (has_parent) {
                marked_to_check.insert(&node.get_parent());
            }
            if(node.get_node_sumID() != 0 && summary_store->id_exists(sumID_full)){
                std::string _logic = options.get_option(HiFrogOptions::LOGIC);
                if (_logic == "prop") {
                    node.set_inline();
                    //remove summary and ID of original full-summary from everywhere
                    summary_store->remove_summary(sumID_full);
                    node.remove_node_sumID(sumID_full); //just deletes from node_summaryID_set
                }
                else if (_logic == "qflra" || _logic == "qfuf") { //if summary is con/dis-junctive, logic could n't be prop.
                
# ifdef DEBUG_HOUDINI
                    std::cout << ";; summary orig is :\n";
                    itpFull.serialize(std::cout);
#endif
                 
                    //Get the args of full-summary and use it in the sub-summary
                    std::vector<PTRef> sumArgs_copy = sumFull->getTempl().getArgs();
                    //Remove full-summary and its ID from everywhere
                    summary_store->remove_summary(sumID_full);
                    node.remove_node_sumID(sumID_full);
                    //node.set_inline(); //not sure
# ifdef HOUDINI_REF
                    summary_idt sub_sumID;
                    if (solver->isConjunctive(sumFull_pref)) {
                        status() << "\n" << "------ " << function_name << "'s summary is  conjunctive!" << eom;
                        //store passed conjuncts and conjoin them later
                        std::vector<PTRef> validConjs{};
                        //Iterate over conjuncts of the full-summary
                        for (int i = 0; i < solver->getLogic()->getPterm(sumFull_pref).size(); i++) {
                            status() << "\n" << "-- checking conjunct: " <<  i+1 << eom;
                            const PTRef subConj_pref = solver->getLogic()->getPterm(sumFull_pref)[i];
#ifdef DEBUG_HOUDINI
                            std::cout <<";; Sub summary is: \n" << solver->getLogic()->pp(subConj_pref) <<"\n";
#endif
                            //Form args of sub_summary based on the full summary
                            smt_itpt_summaryt *sub_sum = solver->create_partial_summary(sumArgs_copy,
                                                                                        node.get_function_id().c_str(),
                                                                                        subConj_pref);
                    // Ask for new ID and add ID <vec>store and <map> funcToid and idTosum
                            sub_sumID = summary_store->insert_summary(sub_sum, node.get_function_id().c_str());
                            //add ID <set> node_summaryID_set
                            node.add_node_sumID(sub_sumID);
                            //Validate new sub summary
                            validated = validate_summary(node, sub_sumID, solver->isConjunctive(sumFull_pref));
                            //regardless of validation result remove summaryID from everywhere; validated conjuncts will be mkAnd
                            summary_store->remove_summary(sub_sumID);
                            node.remove_node_sumID(sub_sumID);
                            if (validated) {
                                validConjs.push_back(subConj_pref);
                                status() << "\n" << "--conjunct " << i + 1 << " was good enough to capture the change of "
                                         << node.get_function_id().c_str() << eom;
                                //add ID once all conjuncts were checked-->mkAnd(valid conj)-->
                                // form summay with suitable args -->insert-summary-store -->update node precision -->increase repaired count
                                //break; //if you find one good summary keep continuing to find more conjuncts and mkAnd them
                            }
                        }
                        if (!validConjs.empty()) {
                            const PTRef weakened_sum_ptref = solver->getLogic()->mkAnd(validConjs);
                            smt_itpt_summaryt *weakened_sum = solver->create_partial_summary(sumArgs_copy,
                                                                                        node.get_function_id().c_str(),
                                                                                             weakened_sum_ptref);
                            //Ask for new ID and insert sumID in both maps funcToid and idTosum
                            sub_sumID = summary_store->insert_summary(weakened_sum, node.get_function_id().c_str());
                            node.add_node_sumID(sub_sumID);
                            node.set_precision(SUMMARY);
                            //increase repaired summary count
                            repaired_nodes.insert(node.get_function_id());
                            status() << "\n" << " weakened summary  composed of " << validConjs.size() << " conjuncts was good enough to capture the change of "
                                     << node.get_function_id().c_str() << eom;
                            //validated = true;//don't do this, because if you call validaye node will have opprtunity to interpolate over subtrees with better itps
                          validated = validate_summary(node, sub_sumID, true);
                        }
                        else { //none of conjuncts was good enough
                            status() << "\n" << "--none of conjuncts was good enough for  "
                                   << node.get_function_id().c_str() << eom;
                            node.set_inline();
                            //ID of original full-summary already was deleted
                        }
                    }
                    else if (solver->isDisjunctive(sumFull_pref)) {
                        status() << "\n" << "------ " << function_name << "'s summary is  disjunctive!" << eom;
                        //Iterate over disjuncts of the full-summary
                        size_t number_of_disjuncts = solver->getLogic()->getPterm(sumFull_pref).size();
                        for (size_t disj = 0; disj < number_of_disjuncts; disj++) {
                            const PTRef one_disjunct = solver->getLogic()->getPterm(sumFull_pref)[disj];
                            if (solver->isConjunctive(one_disjunct)) {
                                // dropping conjuncts inside the disjunctions, but keeping the full disjunctions.
                                //size-1 because you want to keep at least one element in each conjunct
                                Logic::SubstMap subst;
                                size_t number_of_conjuncts = solver->getLogic()->getPterm(one_disjunct).size();
                                for (size_t conj = 0; conj < number_of_conjuncts - 1; conj++) {
                                    const PTRef one_conj = solver->getLogic()->getPterm(one_disjunct)[conj];
#ifdef DEBUG_HOUDINI
                                    std::cout << ";; orig disjunctive sum fla: \n" << solver->getLogic()->pp(sumFull_pref) << "\n\n";
                                    std::cout <<";; a sub-conj to be deleted: \n" << solver->getLogic()->pp(one_conj) <<"\n\n";
#endif
                                    //get rid of one_conj by setting it true
                                    subst.insert(one_conj, solver->getLogic()->getTerm_true());
                                    PTRef res_subst = solver->substitute(sumFull_pref, subst); //sumFull_pref as entire disj fla is kept
                                    // original disjunctive is untouched here
#ifdef DEBUG_HOUDINI
                                    std::cout << ";; res_subst is (got rid of one_conj by setting it true): \n" << solver->getLogic()->pp(res_subst) << "\n";
#endif
                                    //summary args are taken from the full summary
                                    smt_itpt_summaryt *sub_fla_sum = solver->create_partial_summary(sumArgs_copy,
                                                                                                    node.get_function_id().c_str(),
                                                                                                    res_subst);
                                    //Ask for new ID
                                    sub_sumID = summary_store->insert_summary(sub_fla_sum, node.get_function_id().c_str());
                                    node.add_node_sumID(sub_sumID);
                                    //Validate new sub summary
                                    validated = validate_summary(node, sub_sumID, solver->isConjunctive(sumFull_pref));
            
                                    if (!validated) {
                                        //remove summary ID from everywhere
                                        summary_store->remove_summary(sub_sumID);
                                        node.remove_node_sumID(sub_sumID);
                                    } else {
                                        node.add_node_sumID(sub_sumID);
                                        node.set_precision(SUMMARY);
                                        status() << "\n" << "--disjunct " << disj + 1
                                                 << " was good enough to capture the change of "
                                                 << node.get_function_id().c_str() << eom;
                                        //increase repaired summary count
                                        repaired_nodes.insert(node.get_function_id());
                                        break; //if one good summary was found, no need to check other conjuncts.
                                    }
                                } //for loop over conjuncts in DNF
                            }//End of IF Conj
                            if (validated) {
                                //if one good summary from a disjunct was found, no need to check other disjuncts.
                                break;
                            }
                        }
                    }
# endif
                }
            }
        }
        else { //i.e., validated; mark the node that has summery, otherwise parent would not know!
            node.set_precision(SUMMARY);
        }
    }
    return validated;
}
/*******************************************************************\

Function:

// NOTE: checks implication \phi_f => Sum_f.

 Purpose: Checks whether a new implementation of a node still implies
 its original summary?

\*******************************************************************/

bool summary_validationt::validate_summary(call_tree_nodet &node, summary_idt summary_id, bool conjunctive) {
    status() << "------validating summary of " << node.get_function_id().c_str() << " with ID: " << summary_id << eom;
    counter_validation_check++;
    //each time we need a cleaned solver; this resets mainSolver but logic and config stay the same.
    decider->get_solver()->reset_solver();
    
    partitioning_target_equationt equation(ns, *summary_store, true);
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
                               options.get_bool_option("partial-loops")
    };
//  assertion_infot assertion_info((std::vector<goto_programt::const_targett>()));
    assertion_infot assertion_info; // MB: It turns out we need to consider the assertions, in case the summary contains the err symbol.
    symex.set_assertion_info_to_verify(&assertion_info);

    refiner_assertion_sumt refiner {
            *summary_store, omega,
            get_refine_mode(options.get_option("refine-mode")),
            message_handler, omega.get_last_assertion_loc()};
    
    bool assertion_holds = false;
    try {
        assertion_holds = prepareSSA(symex);
        //trivial case without actual solving
        if (assertion_holds) {
            report_success();
            return true;
        }
    }
    catch (const std::string &s) {
        std::cerr << "Error in preparing SSA in finding symbol " << s << ". Invalidate this summary, go to check the parent.\n";
        if (node.node_has_summary()) {
            node.set_inline();
            //remove summary and ID
            summary_store->remove_summary(summary_id);
            node.remove_node_sumID(summary_id);
        }
        return false;
    }
    //obj for managing ssa to smt conversion and then solving
    formula_managert formula_manager{equation, message_handler};

    //local creation of solver; each time a fresh pointer "solver" is created.
    auto solver = decider->get_solver();
    // first partition for the summary to check
    auto interpolator = decider->get_interpolating_solver();
    //refers to entry partition including its subtree
    auto& entry_partition = equation.get_partitions()[0];
    fle_part_idt summary_partition_id = interpolator->new_partition();
    (void)(summary_partition_id);
    
    // f /\ !summary --> ?
    if ((node.node_has_summary()) && summary_store->id_exists(summary_id)) {
        itpt &summary = summary_store->find_summary(summary_id);
        try {
            interpolator->substitute_negate_insert(summary, entry_partition.get_iface().get_iface_symbols());
        }
        catch (SummaryInvalidException &ex) {
            // TODO: figure out a way to check beforehand whether interface matches or not
            // Summary cannot be used for current body -> invalidated
            if (node.node_has_summary() && !conjunctive ) {
                node.set_inline();
                node.set_precision(INLINE);
                //remove summary and ID from everywhere
                summary_store->remove_summary(summary_id);
                node.remove_node_sumID(summary_id);
                //notify partitions about removal of summaries
                //equation.refine_partition(entry_partition.get_iface().partition_id);
                // SA: show me example if you found example requires refine_partition!
                //The method returns right after this point and the equation is destroyed.
                //So no point of calling refine_partition
            }
            return false;
        }
    }
    else { //i.e., there was no summary for node
        return false;
    }
    unsigned iteration_counter = 0;
    while (!assertion_holds)
    {
        iteration_counter++;
        //Converts SSA to SMT formula
        formula_manager.convert_to_formula(*(decider->get_convertor()), *(decider->get_interpolating_solver()));
        // Decides the equation
        bool is_sat = formula_manager.is_satisfiable(*solver);
        assertion_holds = !is_sat;

        if (is_sat) {
            // this refiner can refine if we have summary or havoc representation of a function
            // Else quit the loop! (shall move into a function)
            if (omega.get_summaries_count() == 0 && omega.get_nondets_count() == 0) {
                // nothing left to refine, cex is real -> break out of the refinement loop
                break;
            }
            // Else, try to refine!
            // normal refinement (inline if summary not enough) if
            // it reaches the top-level main and fails --> report immediately
            // 1st figure out functions that can be refined
            refiner.mark_sum_for_refine(*solver, omega.get_call_tree_root(), equation);
            const std::list<call_tree_nodet *> refined_functions = refiner.get_refined_functions();
            if (refined_functions.empty()) {
                // nothing could be refined to rule out the cex, it is real -> break out of refinement loop
                break;
            }
            else {
                //there is room for refinement; remove the summary of functions accumulated in refiner
                for (auto const & refined_node : refined_functions ){
                    if (refined_node->node_has_summary()) {
                        const summary_idt smID = refined_node->get_node_sumID();
                        summary_store->remove_summary(smID);
                        refined_node->remove_node_sumID(smID);
                        refined_node->set_inline();
                        node.set_precision(INLINE);
                        //decrease # of repaired summaries
                        if (repaired_nodes.find(refined_node->get_function_id()) != repaired_nodes.end())
                            repaired_nodes.erase(refined_node->get_function_id());
                    }
                }
                status() << ("Go to next iteration\n") << eom;
                // do the actual refinement of ssa; clear summary info from partition; partition.summary_ID_vec
                refineSSA(symex, refined_functions );
            }
        }
    } // end of refinement loop

    // if true, the assertion has been successfully verified
    const bool is_verified = assertion_holds;
    if (is_verified) {
        // produce and store the summaries
        assert(decider->get_interpolating_solver()->can_interpolate());
        extract_interpolants(equation);
    } // End of UNSAT section
    else // assertion was falsified
    {
        assertion_violated(formula_manager, symex.guard_expln);
    }

    return is_verified;
}
/*******************************************************************\
Function: TIP_sanity_check checks tree interpolation property on the summaries

Purpose: Given a call graph, first it extracts the direct children of each parent
 then checks the tree interpolation property for each subtree
For e.g., in the following call graph:
parent---> direct child
main  ---> phi1
phi1  ---> phi2 phi3
phi3  ---> phi4 phi5
 The sanity check of tree interpolation property (TIP) would be:
 I2 /\ I3 /| Phi1 --> I1
 I4 /\ I5 /| Phi3 --> I3
\*******************************************************************/
void summary_validationt::TIP_sanity_check(vector<call_tree_nodet*>& calls) {

    //associates each parent to its direct children in each subtree
    std::map<call_tree_nodet *, vector<call_tree_nodet *>> map_parent_childs;
    //A container to keep track of insertion order
    std::vector<call_tree_nodet *> insertOrder;
//  for (unsigned i = calls.size() - 1; i > 0; i--) {
//  since calls<> were stored in DFS order, we need reverse order
//  to put the parents in he begining
    for (unsigned i = 2 ; i < calls.size() ; i++) { //cprover_initialize(i=0) and main(i=1) are skipped
        call_tree_nodet *current_node = calls[i];
        //std::cout << "call is : " <<current_node->get_function_id().c_str() << std::endl;
        bool has_parent = current_node->get_function_id() !=  ID_nil && current_node->get_function_id() !=  ID_main;
        if (has_parent) {
            call_tree_nodet * parent = &current_node->get_parent();
            if(map_parent_childs.find(parent) == map_parent_childs.end()){
                //we only add unique parents and skip the repetitive ones
                insertOrder.push_back(parent);
            }
            //don't worry if parent already exists, the current_node will be pushed at the end of vector
            map_parent_childs[parent].push_back(current_node);
        }
    }
    //Debug: prints parents and their direct children based on the order were added
    for (unsigned j = 0; j < insertOrder.size(); j++) {
        std::cout << "Parent: " << insertOrder[j]->get_function_id().c_str();
        std::cout <<" --> Children: " ;
        if(map_parent_childs.find(insertOrder[j])  != map_parent_childs.end()){
            for (auto & child : map_parent_childs[insertOrder[j]]){
                std::cout << child->get_function_id().c_str() << " ";
            }
            std::cout <<'\n';
        }
    }
//  for (auto & map_parent_child : map_parent_childs) {
//      std::cout << "key: " << map_parent_child.first->get_function_id().c_str() << '\n';
//      std::cout <<"values: " ;
//      for(auto element : map_parent_child.second)
//          std::cout << element->get_function_id().c_str() << " ";
//      std::cout <<'\n';
//  }
////iterate over parents and insert each parent and negation of its summary to solve + summary of childs
//  for (auto & map_parent_child : map_parent_childs) {
    bool TIP_preserved = true;
    for (unsigned j = 0; j < insertOrder.size(); j++) {
        call_tree_nodet* current_parent =  insertOrder[j];
        status() << "\n------TIP sanity check " << current_parent->get_function_id().c_str() << " ..." << eom;

        //in each insert do the cleaning
        init_solver_and_summary_store();
        auto solver = decider->get_solver();
        auto interpolator1 = decider->get_interpolating_solver();
        auto convertor1 = decider->get_convertor();
        
        partitioning_target_equationt equation(ns, *summary_store, true);//true:all-claims
    
        std::unique_ptr<path_storaget> worklist;
        symex_assertion_sumt symex{get_goto_functions(),
                                   *current_parent,
                                   options, *worklist,
                                   ns.get_symbol_table(),
                                   equation,
                                   message_handler,
                                   get_goto_functions().function_map.at(
                                           (*current_parent).get_function_id()).body,
                                   omega.get_last_assertion_loc(),
                                   omega.is_single_assertion_check(),
                                   !options.get_bool_option("no-error-trace"),
                                   options.get_unsigned_int_option("unwind"),
                                   options.get_bool_option("partial-loops")
        };
//      assertion_infot assertion_info((std::vector<goto_programt::const_targett>()));
        assertion_infot assertion_info; //It turns out we need to consider the assertions, in case the summary contains the err symbol.
        symex.set_assertion_info_to_verify(&assertion_info);
        status() << "------Using symex the summary of children and root will be added by default" << eom;
        bool implication_holds = prepareSSA(symex);
    
        if (implication_holds) {
            status() << "trivial success " << eom;
        }
        formula_managert ssa_to_formula = formula_managert(equation, message_handler);
    
        // first partition for the summary to check
        // refers to entry partition including its subtree
        auto &entry_partition = equation.get_partitions()[0];
        status() << "------ entry_partition : " << entry_partition.get_iface().function_id.c_str() << eom;
        fle_part_idt summary_partition_id = interpolator1->new_partition();
        (void) (summary_partition_id);
    
        //bool has_summary = !current_parent->get_used_summaries().empty();
        bool has_summary = current_parent->node_has_summary();
        if (has_summary) {
            //const summary_idt parent_sumID = *current_parent->get_used_summaries().begin();
            const summary_idt parent_sumID = current_parent->get_node_sumID();
            itpt &parent_summary = summary_store->find_summary(parent_sumID);
            try {
                status() << "------adding negation of summary of node  : " << entry_partition.get_iface().function_id.c_str() << eom;
                interpolator1->substitute_negate_insert(parent_summary,
                                                       entry_partition.get_iface().get_iface_symbols());
            }
            catch (SummaryInvalidException &ex) {
                // Summary cannot be used for current body -> invalidated
                status() << "------An exception thrown: because Summary cannot be used for the current body" <<eom;
            }
        }
        else {
            continue; //This parent did not have summary. So goto next parent
        }
//        //No need to process the children one by one; it is already covered in symex
//        int size_child = map_parent_child.second.size();
//        for (int j = size_child; j > 0; j--) {
////          in each insert what should be cleaned?
////         init_solver_and_summary_store();
////          auto interpolator2 = decider->get_interpolating_solver();
//
//            auto &child_partition = equation.get_partitions()[j];
//            status() << "------adding summary formula of child : " << child_partition.get_iface().function_id.c_str()
//                     << eom;
//            //child_partition.
//            has_summary = child_partition.has_summary_representation();
//            if (has_summary) {
//                const summary_idt child_sumID = child_partition.summaries[0];
//                const itpt &child_summary = summary_store->find_summary(child_sumID);
//                interpolator1->insert_substituted(child_summary, child_partition.get_iface().get_iface_symbols());
//            }
//        }

        if (!implication_holds) {
            ssa_to_formula.convert_to_formula(*(convertor1),
                                              *(interpolator1));
            // Decides the equation
            bool is_sat = ssa_to_formula.is_satisfiable(*solver);
            implication_holds = !is_sat;
        }

        if (implication_holds) {
            status() << "------Implication holds! " << eom;
        }
        else {
            TIP_preserved = false;
            status() << "------Implication does not hold! "<< eom;
        }
    }
    if (TIP_preserved) {
      status() << "\n------Tree-interpolation property is preserved on the existing summaries! \n" << eom;
    }
    else {
      status() << "\n------Tree-interpolation property is NOT preserved on the existing summaries! \n" << eom;
    }
    exit(0);
}
