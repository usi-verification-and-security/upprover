/*******************************************************************

 Module: Upgrade checker using function summaries.

 Author: Ondrej Sery

\*******************************************************************/

#include "upgrade_checker.h"
#include "diff.h"
#include <string>

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
  bool show_progress)
{
  unsigned long max_mem_used;
  contextt temp_context;
  namespacet ns1(ns.get_context(), temp_context);
  summarizing_checkert sum_checker(program, value_set_analysist(ns1),
                         goto_functions, loopstoret(), loopstoret(),
                         ns1, temp_context, options, std::cout, max_mem_used);

  sum_checker.initialize();

  if(show_progress)
  {
    std::cout << std::endl << "    Checking all claims" << std::endl;
    std::cout.flush();
  }

  // Check all the assertions
  bool result = sum_checker.assertion_holds(assertion_infot(), true);
  
  sum_checker.serialize();

  if (!result){
    std::cout << "Upgrade checking is not possible." << std::endl
        << "Try standalone verification." << std::endl;
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
  bool show_progress) 
{
  // 1. Make diff
  // 2. Construct changed summary_info tree -> write back to "__omega"

  fine_timet initial, final;
  initial=current_time();

  bool res = difft(goto_functions_old, goto_functions_new, "__omega").do_diff();

  final = current_time();
  std::cout << std::endl<< "DIFF TIME: " << time2string(final - initial) << std::endl;

  if (res){
    std::cout<< "The programs are trivially identical." << std::endl;
    return 0;
  }


  unsigned long max_mem_used;
  contextt temp_context;
  namespacet ns1(ns.get_context(), temp_context);
  upgrade_checkert upg_checker(program_new, value_set_analysist(ns1),
                         goto_functions_new, loopstoret(), loopstoret(),
                         ns1, temp_context, options, std::cout, max_mem_used);

  // Load older summaries
  upg_checker.initialize();

  if(show_progress)
  {
    std::cout << std::endl << "    Checking all claims" << std::endl;
    std::cout.flush();
  }

  return upg_checker.check_upgrade();
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
  omega.deserialize("__omega", goto_program);
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
    if (omega.get_last_assertion_loc() >= (*summs[i]).get_call_location()){
      upward_traverse_call_tree((*summs[i]), res);
    } else {
      std::cout << "ignoring function: " << (*summs[i]).get_function_id()
            << " (loc. number " << (*summs[i]).get_call_location() << " is out of assertion scope)\n";
    }
    if (!res) {
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
  
  omega.serialize_xml(options.get_option("save-change-impact"));
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
  std::cout << "checking function: " << summary_info.get_function_id() << "\n";
  if (!summary_info.is_preserved_node() || !pre){
    if (!summary_info.is_preserved_node()){
      std::cout << "  -- the body is changed;";
    }
    if (summary_info.get_precision() == 1 || !pre){
      if (summary_info.get_precision() == 1){
        std::cout << " and there was a summary. ";
      } else {
        std::cout << "   [parent check] do inlining.\n";
      }
      // prepare subst. scenario for reverification
      downward_traverse_call_tree (summary_info);

      //TODO: then do the real check + refinement, if needed
      //      in case of refinement, subst scenario will be renewed
      pre = check_summary(assertion_infot(), summary_info);
      if (pre){
        std::cout << "  summary was verified. go to the next check\n"; // here is the actual exit of the method
        summary_info.set_summary();
        // TODO: renew summaries at the store:
        //       the new one may be either strengthening of the old one, or inconsistent
      } else {
        if (summary_info.get_parent().is_root()){
          std::cout << "summary cannot be renewed. A real bug found. ";
        } else {
          std::cout << "check the parent.\n";
          summary_info.set_inline();
          summarization_context.set_valid_summaries(summary_info.get_function_id(), false);
          std::cout << "invalidating summary: " << summary_info.get_function_id() << "\n";
          upward_traverse_call_tree(summary_info.get_parent(), pre);
        }
      }

    } else {
      std::cout << "  it's probably ok for a while. we will return to here, it will be required from higher calls;";
    }
  } else {
    std::cout << "  preserved. go to the next check\n";
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
    std::cout << "\n    -- the function call of " << (it->second).get_function_id();

    if (it->second.is_preserved_edge()){
      std::cout << " is preserved;";
      // FIXME: a summary that was being verified (both, valid or not) is INL now
      if ((it->second).get_precision() == 1){
        std::cout << " has summary => can be kept ";
      } else if ((it->second).get_precision() == 0){
        std::cout << " was havoced (probably, out of las_assertion_loc) => can be kept ";
      } else {
        if ((it->second).has_assertion_in_subtree()){
          std::cout << " was inlined (since has assertion) can be kept" ;
          // if inline, then do recursive traverse downward
          downward_traverse_call_tree(it->second);
        } else {
          std::cout << " was inlined (irrelevant for proof) => can be havoced";
          (it->second).set_nondet();
        }
      }

    } else {
      std::cout << " not preserved => do inlining";
    }
    std::cout <<"\n";
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
    out << std::endl << "ASSERTION IS TRIVIALLY TRUE" << std::endl;
    return true;
  }
  const bool no_slicing_option = options.get_bool_option("no-slicing");

  const unsigned last_assertion_loc = omega.get_last_assertion_loc();
  const bool single_assertion_check = omega.is_single_assertion_check();

  partitioning_target_equationt equation(ns, summarization_context, true, true);

  symex_assertion_sumt symex = symex_assertion_sumt(
            summarization_context, summary_info, ns, context,
            equation, out, goto_program, last_assertion_loc,
            single_assertion_check, !no_slicing_option);

  setup_unwind(symex);
  symex.loop_free_check();

  refiner_assertion_sumt refiner = refiner_assertion_sumt(
              summarization_context, omega, equation,
              get_refine_mode(options.get_option("refine-mode")),
              out, last_assertion_loc, false);

  prop_assertion_sumt prop = prop_assertion_sumt(summarization_context,
          equation, out, max_memory_used);
  unsigned count = 0;
  bool end = false;

  while (!end && count < (unsigned)options.get_int_option("steps"))
  {
    count++;
    opensmt = new satcheck_opensmtt(
      options.get_int_option("verbose-solver"),
      options.get_bool_option("save-queries"));
    interpolator.reset(opensmt);
    bv_pointerst *deciderp = new bv_pointerst(ns, *opensmt);
    deciderp->unbounded_array = bv_pointerst::U_AUTO;
    decider.reset(deciderp);

    end = (count == 1) ? symex.prepare_subtree_SSA(assertion) :
          symex.refine_SSA (assertion, refiner.get_refined_functions(), true);

    if (!end){

      end = prop.assertion_holds(assertion, ns, *decider, *interpolator);
      unsigned summaries_count = omega.get_summaries_count(summary_info);
      if (end && interpolator->can_interpolate())
      {
        double red_timeout = compute_reduction_timeout((double)prop.get_solving_time());
        extract_interpolants(equation, red_timeout);
        //omega.serialize("__omega_" + i2string(omega.get_assertion_location(assertion.get_location())));
        out << "Old summary is still valid";
        if (summaries_count == 0)
        {
          out << " (after inlining)." << std::endl;
        } else {
          out << " (after " << summaries_count <<
                  " successful sub-summaries substitutions)." << std::endl;
        }
      } else {
        if (summaries_count != 0 || init == ALL_HAVOCING) {
//          if (init == ALL_HAVOCING){
//            out << "NONDETERMINISTIC ASSIGNMENTS FOR ALL FUNCTION CALLS ";
//          } else {
            out << "Function summaries (for " << summaries_count << " calls) ";
//        }
          out << "are not suitable for re-verification the summary." << std::endl;
          refiner.refine(*decider, summary_info);

          if (refiner.get_refined_functions().size() == 0){
            out << "Old summary is no more valid." << std::endl;
            break;
          } else {
            out << "Counterexample is spurious."  << std::endl <<
                   "Go to next iteration." << std::endl;
          }
        } else if (omega.get_nondets_count() != 0) {
              // if there are still some havoced function calls, do force inlining for them
          refiner.set_refine_mode(FORCE_INLINING);
          refiner.refine(*decider, summary_info);
          out << "Go to next iteration." << std::endl;
        } else {
          out << "Old summary is no more valid."  << std::endl;
          break;
        }
      }
    }
  }
  final = current_time();

  out << std::endl<< "Total number of steps: " << count << "." << std::endl <<
        "TOTAL TIME FOR CHECKING THIS SUMMARY: "<< time2string(final - initial) << std::endl;
  return end;
}
