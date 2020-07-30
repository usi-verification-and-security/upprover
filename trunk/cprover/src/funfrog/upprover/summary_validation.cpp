/*******************************************************************

 Module: UpProver: Incremental verification of changes using function summaries.

\*******************************************************************/
#include <funfrog/partitioning_target_equation.h>
#include <goto-symex/path_storage.h>
#include <funfrog/symex_assertion_sum.h>
#include <funfrog/refiner_assertion_sum.h>
#include <funfrog/prepare_formula.h>
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
    bool res_diff = diff.do_diff(goto_model_old.goto_functions, goto_model_new.goto_functions); //false means at least one function has changed
    auto after = timestamp();
    msg.status() << "DIFF TIME: " << time_gap(after,before) << msg.eom;
    if (res_diff){
        msg.status() << "The program models are identical" <<msg.eom;
        if(!options.is_set("sanity-check")){
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
// Here we suppose that "__omega" already contains information about changes
// TODO: Maybe omega should be passed internally, not as a file.
    omega.deserialize(options.get_option("save-omega"),
            goto_model.goto_functions.function_map.at(goto_functionst::entry_point()).body); //double check restore_call_info
    omega.process_goto_locations();
    omega.setup_last_assertion_loc(assertion_infot());
    // init solver and load older summaries in the same way as hifrog
    init_solver_and_summary_store();
    
    std::vector<call_tree_nodet*>& calls = omega.get_call_summaries();
    if(options.is_set("sanity-check")){
       sanity_check(calls);
    }
    std::unordered_set<call_tree_nodet*> marked_to_check;
    bool validated = false;
    auto before_iteration_over_functions = timestamp();
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
            // The subtrees in call_tree_nodes have the correct information about summaries
            //if validated summaries for subtrees are updated in extract_interpolaion
            // make sure the new summary was added, or replaced the old summaries correctly
            if(current_node.get_function_id() == ID_main){
                // Final check:  main function does not have a summary form previous run (i.e., false summary)
                // perform a classic HiFrog check and normal refinement (inline if summary not enough) if
                // it reaches the top-level main and fails --> report immediately
                status() << "\nFinal validation node " << function_name << " ..." << eom;
                init_solver_and_summary_store();
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
    auto after_iteration_over_functions  = timestamp();
    status() << "\nTotal iteration TIME over ALL functions for node validation (includes sub-SYMEX+CONVERSION+SOLVING times): "
             << time_gap(after_iteration_over_functions,before_iteration_over_functions) << eom;
    //Final conclusion
    if (validated) {
        status() << "\nThe whole call tree has been validated!" << eom;
    }
    else {
        status() << "Validation failed! A real bug found. " << eom;
        report_failure();
        return false;
    }
    //update __omega file
    serialize();
    
    report_success();
    return true;
}

/*******************************************************************\
Function:

Purpose: Triggers validation of summary associated with the node
Note: Obtain summaries based on call-nodes, not function name(as different nodes can have different summaries)
// hack to update the summaryFile for the next occasion(for e.g, we will need the updated summaries
// for the next decider which will read this summaryFile to update the summary_storet)
// TODO: later make decider and summary store independent
\*******************************************************************/
bool summary_validationt::validate_node(call_tree_nodet &node) {
    
    const std::string function_name = node.get_function_id().c_str();
    bool validated = false;
    status() << "\n------validating node " << function_name << " ..." << eom;
    bool has_summary;
    //has_summary = summary_store->has_summaries(function_name);
    has_summary = !node.get_used_summaries().empty();
    if (has_summary){
        //for now we only consider one summary per node
        //there is only one summary per node due to full unrolling using goto-instrument
//      const summary_idt single_sumID2 = summary_store->get_summariesID(function_name)[0];//always take the same ID for all, obviously wrong
        const summary_idt full_sumID = *(node.get_used_summaries().begin());
//      status() << "size of set of ids: " <<node.get_used_summaries().size() << "   single_sumID: " << single_sumID <<eom;
//      print summary-in-use in the console
//      itpt_summaryt& currentSum = summary_store->find_summary(single_sumID);
//      currentSum.serialize(std::cout);
        validated = validate_summary(node , full_sumID);
        if (!validated) {
            //invalidates summary for call tree node -> remove summary_id and set precision
            //                                       -> delete summary itself from summary store
            std::shared_ptr<summary_storet> summary_store_backup = this->summary_store;
            itpt_summaryt& currentSum_total = summary_store_backup->find_summary(full_sumID);
            smt_itpt_summaryt* sum_total = dynamic_cast<smt_itpt_summaryt*>(&currentSum_total);
            PTRef currentSum_PTRef = sum_total->getInterpolant();
            //get an access to the solver
            //and make a backup as it is needed for next iteration
            auto decider_backup = this->decider;  //shared_ptr
            smtcheck_opensmt2t* solver = dynamic_cast<smtcheck_opensmt2t*>(decider_backup->get_solver());
            //when initialize_solver() assign a new object to decider, solver and decider_backup were preserved alive.
            assert(solver);
            //if summary is conjunctive -- logic is not prop. Note: summary of each function has single ID and single PTref
            //drop one conjunct per time: add the resultant summary to summary_storet and ask for new ID;remove old summary
            if(solver->isConjunctive(currentSum_PTRef)) {
                std::cout <<"it's conjunctive!" <<"\n";
                std::cout <<solver->getLogic()->printTerm(currentSum_PTRef) <<"\n";
                //iterate over conjuncts
                for (int i = 0; i < solver->getLogic()->getPterm(currentSum_PTRef).size(); i++) {
                    PTRef c = solver->getLogic()->getPterm(currentSum_PTRef)[i];
                    std::cout <<";sub summary associated with ptref " << c.x << " is: \n" << solver->getLogic()->pp(c) <<"\n";
                    //for sub_sum we use the template of sum_total that was filled in generalize_summary(),
                    smt_itpt_summaryt* sub_sum =  solver->create_partial_summary(sum_total, node.get_function_id().c_str(), c);
//                  get ID for new sub-summary
                    auto sub_sumID  = summary_store_backup->insert_summary(sub_sum,node.get_function_id().c_str());
                    //node.add_summary_IDs(sub_sumID); //too soon to add;lets add it when was validated
                    //store summary in the file
                    summary_store_backup->serialize(options.get_option(HiFrogOptions::SAVE_FILE));
                    //validate new sub summary
                    validated = validate_summary(node, sub_sumID);
                    if(!validated) {
                        //node.remove_summaryID(sub_sumID); //we didn't add ID
                        //remove summary ID from summary store
                        summary_store_backup->remove_summary(sub_sumID);
                        summary_store_backup->decrease_max_id();
                    }
                    else {
                        node.add_summary_IDs(sub_sumID);
                        node.set_precision(SUMMARY);
                        break; //if you find one good summary no need to continue other conjuncts.
                    }
                }
            }
            node.remove_summaryID(full_sumID); //does n't remove completely from summary_store, just remove from summary_ID_set
            node.set_inline();
            summary_store_backup->remove_summary(full_sumID);
            summary_store_backup->serialize(options.get_option(HiFrogOptions::SAVE_FILE));
        }
        else { //mark the node that has summery, otherwise parent would not know!
            node.set_precision(SUMMARY);
        }
    }
    return validated;
}
/*******************************************************************\

Function:

// NOTE: checks implication \phi_f => I_f.

 Purpose: Checks whether a new implementation of a node still implies
 its original summary?

\*******************************************************************/

bool summary_validationt::validate_summary(call_tree_nodet &node, summary_idt summary_id) {
    //each time we need a cleaned solver, otherwise old solver conflicts with new check; in the classical check also we init first.
    //SA: did we add something to the summary store? make sure not!
    status() << "------validating summary " << node.get_function_id().c_str() << " ..." << eom;
    init_solver_and_summary_store();
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
                               options.get_bool_option("partial-loops"),
    };
//    assertion_infot assertion_info((std::vector<goto_programt::const_targett>()));
    assertion_infot assertion_info; // MB: It turns out we need to consider the assertions, in case the summary contains the err symbol.
    symex.set_assertion_info_to_verify(&assertion_info);

    refiner_assertion_sumt refiner {
            *summary_store, omega,
            get_refine_mode(options.get_option("refine-mode")),
            message_handler, omega.get_last_assertion_loc()};

    bool assertion_holds = prepareSSA(symex);
    //trivial case without actual solving
    if (assertion_holds){
        report_success();
        return true;
    }

    // the checker main loop:
    unsigned summaries_used = 0;
    unsigned iteration_counter = 0;
    prepare_formulat ssa_to_formula = prepare_formulat(equation, message_handler);

    //local creation of solver; in every call a fresh raw pointer "solver" pointing to decider is created.
    //but be careful decider(which is member variable of core_checker) will be alive after validate_summary()
    //is done. So raw pointer solver gets out-of-scope, but decider is still around and
    // will mess up with the next check. At the moment opensmt does not have method for cleaning
    //and temporarily we do init_solver_and_summary_store(); for this purpose in the beginning.
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
Function: sanity_check for tree interpolation property

Purpose: Given a call graph, first it extracts the direct children of each parent
 then checks the tree interpolation property for each subtree
For e.g., in the following call graph:
parent---> direct child
main  ---> phi1
phi1  ---> phi2 phi3
phi3  ---> phi4 phi5
 The sanity check would be:
 I2 /\ I3 /| Phi1 --> I1
 I4 /\ I5 /| Phi3 --> I3
\*******************************************************************/
void summary_validationt::sanity_check(vector<call_tree_nodet*>& calls) {

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
    for (unsigned j = 0; j < insertOrder.size(); j++) {
        call_tree_nodet* current_parent =  insertOrder[j];
        status() << "\n------sanity check " << current_parent->get_function_id().c_str() << " ..." << eom;

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
                                   options.get_bool_option("partial-loops"),
        };
//      assertion_infot assertion_info((std::vector<goto_programt::const_targett>()));
        assertion_infot assertion_info; //It turns out we need to consider the assertions, in case the summary contains the err symbol.
        symex.set_assertion_info_to_verify(&assertion_info);
        status() << "------Using symex the summary of children and root will be added by default" << eom;
        bool implication_holds = prepareSSA(symex);
    
        if (implication_holds) {
            status() << "trivial success " << eom;
        }
        prepare_formulat ssa_to_formula = prepare_formulat(equation, message_handler);
    
        // first partition for the summary to check
        // refers to entry partition including its subtree
        auto &entry_partition = equation.get_partitions()[0];
        status() << "------ entry_partition : " << entry_partition.get_iface().function_id.c_str() << eom;
        fle_part_idt summary_partition_id = interpolator1->new_partition();
        (void) (summary_partition_id);
    
        bool has_summary = !current_parent->get_used_summaries().empty();
        if (has_summary) {
            const summary_idt parent_sumID = *current_parent->get_used_summaries().begin();
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
            status() << "------Implication does not hold! " << eom;
        }
    }
    exit(0);
}
