/*******************************************************************

 Module: Upgrade checker using function summaries.

 Author: Ondrej Sery

\*******************************************************************/

#include "upgrade_checker.h"
#include "diff.h"
#include <string>
#include <i2string.h>

void upgrade_checkert::initialize()
{
    // Prepare the summarization context
  summarization_context.analyze_functions(ns);

  // Load older summaries
  {
    const std::string& summary_file = options.get_option("load-summaries");
    if (!summary_file.empty()) {
      summarization_context.deserialize_infos(summary_file);
    }
  }
}

/*******************************************************************\

Function: check_initial

  Inputs:

 Outputs:

 Purpose: Check the whole system and prepare for incremental 
 check of upgrades via check_upgrade.

\*******************************************************************/

bool check_initial(const namespacet &ns,
  goto_programt &program,
  const goto_functionst &goto_functions,
  const optionst& options,
  ui_message_handlert &message_handler,
  bool show_progress)
{
  unsigned long max_mem_used;
  contextt temp_context;
  namespacet ns1(ns.get_symbol_table(), temp_context);
  summarizing_checkert sum_checker(program,
       goto_functions, ns1, temp_context, options, message_handler, max_mem_used);

  sum_checker.initialize();

  if(show_progress)
  {
    sum_checker.status("Checking all claims");
    //std::cout.flush();
  }

  // Check all the assertions
  bool result = sum_checker.assertion_holds(assertion_infot(), true);
  
  sum_checker.serialize();

  if (!result){
    sum_checker.status("Upgrade checking is not possible");
    sum_checker.status("Try standalone verification");
  }

  return result;
}

/*******************************************************************\

Function: check_upgrade

  Inputs:

 Outputs:

 Purpose: Incremental check of the upgraded program.

\*******************************************************************/
bool check_upgrade(const namespacet &ns,
  goto_programt &program_old,
  goto_functionst &goto_functions_old,
  goto_programt &program_new,
  goto_functionst &goto_functions_new,
  const optionst& options,
  ui_message_handlert &message_handler,
  bool show_progress) 
{
  // 1. Make diff
  // 2. Construct changed summary_info tree -> write back to "__omega"


  fine_timet initial, final;
  initial=current_time();

  std::ifstream in;
  in.open(options.get_option("load-omega").c_str());

  if (in.fail()){
    std::cerr << "Failed to deserialize previous verification efforts (file: " <<
        options.get_option("load-omega").c_str() <<
            " cannot be read)" << std::endl;
    return 1;
  }

  difft diff(message_handler, goto_functions_old, goto_functions_new,
      options.get_option("load-omega").c_str(), options.get_option("save-omega").c_str());

  bool res = diff.do_diff();

  final = current_time();
  diff.status() << "DIFF TIME: " << (final - initial) << diff.eom;
  if (res){
    diff.status("The program models are identical");
    return 0;
  }


  unsigned long max_mem_used;
  contextt temp_context;
  namespacet ns1(ns.get_symbol_table(), temp_context);
  upgrade_checkert upg_checker(program_new,
         goto_functions_new, ns1, temp_context, options, message_handler, max_mem_used);

  // Load older summaries
  upg_checker.initialize();

  if(show_progress)
  {
    //upg_checker.status("Checking all claims");
    //std::cout.flush();
  }

  res = upg_checker.check_upgrade();

  final = current_time();

  upg_checker.status() << "TOTAL UPGRADE CHECKING TIME: " << (final - initial) << upg_checker.eom;

  upg_checker.save_change_impact();

  return res;
}

/*******************************************************************\

Function: upgrade_checkert::check_upgrade

  Inputs:

 Outputs:

 Purpose: Incremental check of the upgraded program.

\*******************************************************************/
bool upgrade_checkert::check_upgrade() 
{

  // Here we suppose that "__omega" already contains information about changes
  // TODO: Maybe omega should be passed internally, not as a file.
  omega.deserialize(options.get_option("save-omega"), goto_program);
  omega.process_goto_locations();
  omega.setup_last_assertion_loc(assertion_infot());

  // 3. Mark summaries as
  //     - valid: the function was not changed                  => summary_info.preserved_node == true
  //     - invalid: interface change                            [TBD], for now, all of them are 'unknown'
  //                                / ass_in_subtree change     [TBD], suppose, every ass_in_subtree preserved
  //     - unknown: function body changed                       => summary_info.preserved_node == false

  std::vector<summary_infot*>& summs = omega.get_call_summaries();
  for (unsigned i = summs.size() - 1; i > 0; i--){
    // backward search, from the summary with the largest call location

    bool res = true;

    const irep_idt& name = (*summs[i]).get_function_id();

#ifdef DEBUG_UPGR
    std::cout << "checking summary #"<< i << ": " << name <<"\n";
#endif
    // if (omega.get_last_assertion_loc() >= (*summs[i]).get_call_location()){

      const summary_ids_sett& used = (*summs[i]).get_used_summaries();
      if (used.size() == 0 && !(*summs[i]).is_preserved_node()){
        res = false;
        upward_traverse_call_tree((*summs[i]).get_parent(), res);
      }

      for (summary_ids_sett::const_iterator it = used.begin(); it != used.end(); ++it) {
//        summaryt& summary = summarization_context.get_summary_store().find_summary(*it);
//        summary.print(std::cout);

        if (checked_summaries.find(*it) == checked_summaries.end()){
          summary_ids_sett summary_to_check;
          summary_to_check.insert(*it);
          (*summs[i]).set_used_summaries(summary_to_check);
          upward_traverse_call_tree((*summs[i]), res);
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
      status() << "Invalid summaries ratio: " << omega.get_invalid_count() << "/" << (omega.get_call_summaries().size() - 1) << eom;
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
  
  status() << "Invalid summaries ratio: " << omega.get_invalid_count() << "/"  << (omega.get_call_summaries().size() - 1) << eom;
  serialize();
  report_success();
  return true;
}

/*******************************************************************\

Function: upgrade_checkert::upward_traverse_call_tree

  Inputs:

 Outputs:

 Purpose: Traverses the function call stack to check the change,
          if the down-more attempt failed (pre == false)
          or from scratch (pre == true)

\*******************************************************************/
void upgrade_checkert::upward_traverse_call_tree(summary_infot& summary_info, bool& pre)
{
  status() << "checking validity of old summary for function: " << summary_info.get_function_id() << eom;
  const summary_ids_sett& used = summary_info.get_used_summaries();
  assert(used.size() <= 1); // we can check only one summary at a time

  for (summary_ids_sett::const_iterator it = used.begin(); it != used.end(); ++it){
    checked_summaries.insert(*it);
  }
  if (!summary_info.is_preserved_node() || !pre){
#ifdef DEBUG_UPGR
    if (!summary_info.is_preserved_node()){
      std::cout << "  -- the body is changed;";
    }
#endif
    if (summary_info.get_precision() == 1){
#ifdef DEBUG_UPGR
      if (summary_info.get_precision() == 1){
        std::cout << " and there was a summary.\n";
      } else {
        std::cout << "   [parent check] do inlining.\n";
      }
#endif
      // prepare subst. scenario for reverification
      downward_traverse_call_tree (summary_info);

      //TODO: then do the real check + refinement, if needed
      //      in case of refinement, subst scenario will be renewed
      pre = check_summary(assertion_infot(), summary_info);
      if (pre){
    	  status("  summary was verified. go to the next check."); // here is the actual exit of the method
        summary_info.set_summary();
      } else {
        summarization_context.set_valid_summaries(summary_info.get_function_id(), false);
        status() << "invalidating summary: " << summary_info.get_function_id() << eom;
        summary_info.clear_used_summaries();
        if (summary_info.get_parent().is_root()){
          status("summary cannot be renewed. A real bug found. ");
        } else {
          status("check the parent.");
          summary_info.set_inline();
          upward_traverse_call_tree(summary_info.get_parent(), pre);
        }
      }

    } else {
      //std::cout << "  no summary, but the code was changed. try checking the parent.\n";
      summarization_context.set_valid_summaries(summary_info.get_function_id(), false);
      summary_info.set_inline();
      pre = false;
      upward_traverse_call_tree(summary_info.get_parent(), pre);
    }
  } else {
    status("  preserved. go to the next check.");
  }
}


/*******************************************************************\

Function: upgrade_checkert::downward_traverse_call_tree

  Inputs:

 Outputs:

 Purpose: Traverses the function call tree in order to re-configure
          subst. scenario for re-verifying a summary

\*******************************************************************/
void upgrade_checkert::downward_traverse_call_tree(summary_infot& summary_info)
{
  call_sitest call_sites = summary_info.get_call_sites();
  for (call_sitest::iterator it = call_sites.begin();
          it != call_sites.end(); ++it)
  {
#ifdef DEBUG_UPGR
    std::cout << "\n    -- the function call of " << (it->second).get_function_id();
#endif
    if (it->second.is_preserved_edge()){
#ifdef DEBUG_UPGR
      std::cout << " is preserved;";
#endif
      // FIXME: a summary that was being verified (both, valid or not) is INL now
      if ((it->second).get_precision() == 1){
#ifdef DEBUG_UPGR
        std::cout << " has summary => will remain summarized ";
#endif
      } else if ((it->second).get_precision() == 0){
#ifdef DEBUG_UPGR
        std::cout << " was havoced (probably, out of las_assertion_loc) => will remain havoced";
#endif
      } else {
        if ((it->second).has_assertion_in_subtree()){
#ifdef DEBUG_UPGR
          std::cout << " was inlined (since has assertion) => will remain inlined" ;
#endif
          // if inline, then do recursive traverse downward
          downward_traverse_call_tree(it->second);
        } else if ((it->second).is_preserved_node()){
#ifdef DEBUG_UPGR
          std::cout << " was inlined (irrelevant for proof) => can be havoced";
#endif
          (it->second).set_nondet();
        } else {
#ifdef DEBUG_UPGR
          std::cout << " was modified => should be inlined";
#endif
        }
      }

    } else {
#ifdef DEBUG_UPGR
      std::cout << " not preserved => do inlining";
#endif
    }
#ifdef DEBUG_UPGR
    std::cout <<"\n";
#endif
  }
}

/*******************************************************************\

Function: upgrade_checkert::check_summary

  Inputs:

 Outputs:

 Purpose: Checks whether an implementation of a function still implies
 its original summary.

\*******************************************************************/

bool upgrade_checkert::check_summary(const assertion_infot& assertion,
        summary_infot& summary_info)
{
  fine_timet initial, final;
  initial=current_time();
  // Trivial case
  if(assertion.is_trivially_true())
  {
    status("ASSERTION IS TRIVIALLY TRUE");
    report_success();
    return true;
  }
  const bool no_slicing_option = options.get_bool_option("no-slicing");

  const unsigned last_assertion_loc = omega.get_last_assertion_loc();
  const bool single_assertion_check = omega.is_single_assertion_check();

  std::vector<unsigned> ints;

  // so far, partial interpolation is disabled in the upgrade checking scenario

  partitioning_target_equationt equation(ns, summarization_context, true, true, NO_COLORING, ints);

  symex_assertion_sumt symex = symex_assertion_sumt(
            summarization_context, summary_info, ns, symbol_table,
            equation, message_handler, goto_program, last_assertion_loc,
            single_assertion_check, !no_slicing_option);

  setup_unwind(symex);

  refiner_assertion_sumt refiner = refiner_assertion_sumt(
              summarization_context, omega, equation,
              get_refine_mode(options.get_option("refine-mode")),
              message_handler, last_assertion_loc, false);

  prop_assertion_sumt prop = prop_assertion_sumt(summarization_context,
          equation, message_handler, max_memory_used);
  unsigned count = 0;
  bool end = false;

  while (!end)
  {
    count++;

    decider = new smtcheck_opensmt2t_lra();

//    interpolator.reset(opensmt);
//    bv_pointerst *deciderp = new bv_pointerst(ns, *opensmt);
//    deciderp->unbounded_array = bv_pointerst::U_AUTO;
//    decider.reset(deciderp);

    end = (count == 1) ? symex.prepare_subtree_SSA(assertion) :
          symex.refine_SSA (assertion, refiner.get_refined_functions(), true);

    if (!end){

      end = prop.assertion_holds(assertion, ns, *decider, *decider);
      unsigned summaries_count = omega.get_summaries_count(summary_info);
      if (end && decider->can_interpolate())
      {
        extract_interpolants(prop, equation);
        status("Old summary is still valid");
        if (summaries_count == 0)
        {
          //std::cout << " (after inlining)." << std::endl;
        } else {
          //std::cout << " (after successful substitution of " << summaries_count <<
          //        " summaries for nested function calls)." << std::endl;
        }
      } else {
        if (summaries_count != 0 || init == ALL_HAVOCING) {
//          if (init == ALL_HAVOCING){
//            out << "NONDETERMINISTIC ASSIGNMENTS FOR ALL FUNCTION CALLS ";
//          } else {
            //std::cout << "Function summaries (for " << summaries_count << " calls) ";
//        }
          //std::cout << "are not suitable for re-verification the summary." << std::endl;
          refiner.refine(*decider, summary_info);

          if (refiner.get_refined_functions().size() == 0){
            //std::cout << "Old summary is no more valid." << std::endl;
            break;
          } else {
            //std::cout << "Counterexample is spurious."  << std::endl <<
            //       "Go to the next iteration." << std::endl;
          }
        } else {
          //std::cout << "Old summary is no more valid."  << std::endl;
          break;
        }
      }
    }
  }
  final = current_time();
  if (!end && summary_info.get_parent().is_root()){
    prop.error_trace(*decider, ns, symex.guard_expln);
  }
  status() << "Total number of steps: " << count << eom;
  status() << "TOTAL TIME FOR CHECKING THIS SUMMARY: " << (final - initial) << eom;
  return end;
}

/*
  same as method as its predecessor, but it marks all newly generated interpolants as 'checked'
*/
void upgrade_checkert::extract_interpolants (prop_assertion_sumt& prop, partitioning_target_equationt& equation)
{
  summary_storet& summary_store = summarization_context.get_summary_store();
  interpolant_mapt itp_map;
  fine_timet before, after;
  before=current_time();

  equation.extract_interpolants(*decider, *decider, itp_map);

  after=current_time();
  status() << "INTERPOLATION TIME: " << (after-before) << eom;

  for (interpolant_mapt::iterator it = itp_map.begin();
                  it != itp_map.end(); ++it) {
    summary_infot& summary_info = it->first->summary_info;

    function_infot& function_info =
            summarization_context.get_function_info(
            summary_info.get_function_id());

    function_info.add_summary(summary_store, it->second, false
            /*!options.get_bool_option("no-summary-optimization")*/);

    summary_info.add_used_summary(it->second);
    checked_summaries.insert(it->second);        // skip recheking a newly generated summary
    summary_info.set_summary();           // helpful flag for omega's (de)serialization
  }
  // Store the summaries
  const std::string& summary_file = options.get_option("save-summaries");
  if (!summary_file.empty()) {
    summarization_context.serialize_infos(summary_file,
            omega.get_summary_info());
  }
}
