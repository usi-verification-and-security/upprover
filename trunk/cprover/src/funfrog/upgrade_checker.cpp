/*******************************************************************

 Module: Upgrade checker using function summaries.

 Author: Ondrej Sery

\*******************************************************************/

#include "upgrade_checker.h"
#include "diff.h"
#include <string>

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
  bool result = sum_checker.assertion_holds(assertion_infot());
  
  sum_checker.serialize();
  
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

  bool res = difft().do_diff(goto_functions_old, goto_functions_new, "__omega");

  if (res){
    std::cout<< "The programs are trivially identical." << std::endl;
    return 0;
  }

  unsigned long max_mem_used;
  contextt temp_context;
  namespacet ns1(ns.get_context(), temp_context);
  upgrade_checkert upg_checker(program_old, value_set_analysist(ns1),
                         goto_functions_old, loopstoret(), loopstoret(),
                         ns1, temp_context, options, std::cout, max_mem_used);

  //upg_checker.initialize();

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

  // 3. Mark summaries as
  //     - valid: the function was not changed
  //     - invalid: interface change / ass_in_subtree change
  //     - unknown: function body changed
  // 3. From the bottom of the tree, reverify all changed nodes
  //    a. If the edge is unchanged, check implication of previously 
  //       used summaries
  //        - OK/already valid: summary valid, don't propagate check upwards
  //        - KO/already invalid: summary invalid, propagate check upwards
  //    b. If the edge is changed, propagate check upwards (we don't know which summary 
  //       to check).
  //
  // NOTE: call check_summary to do the check \phi_f => I_f.
  
  assert(false);
  return false;
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
  assert(false);
  
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

  partitioning_target_equationt equation(ns, summarization_context);

  symex_assertion_sumt symex = symex_assertion_sumt(
            summarization_context, summary_info, ns, context,
            equation, out, goto_program, !no_slicing_option);

  setup_unwind(symex);
  symex.loop_free_check();

  refiner_assertion_sumt refiner = refiner_assertion_sumt(
              summarization_context, omega, equation,
              get_refine_mode(options.get_option("refine-mode")),
              out, last_assertion_loc);

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

    end = (count == 1) ? symex.prepare_subtree_SSA(assertion) : symex.refine_SSA (assertion, refiner.get_refined_functions());

    if (!end){

      end = prop.assertion_holds(assertion, ns, *decider, *interpolator);
      unsigned summaries_count = omega.get_summaries_count();
      if (end && interpolator->can_interpolate())
      {
        double red_timeout = compute_reduction_timeout((double)prop.get_solving_time());
        extract_interpolants(equation, red_timeout);
        //omega.serialize("__omega_" + i2string(omega.get_assertion_location(assertion.get_location())));
        if (summaries_count == 0)
        {
          out << "ASSERTION(S) HOLD(S) AFTER INLINING." << std::endl;
        } else {
          out << "FUNCTION SUMMARIES (for " << summaries_count <<
                  " calls) WERE SUBSTITUTED SUCCESSFULLY." << std::endl;
        }
      } else {
        if (summaries_count != 0 || init == ALL_HAVOCING) {
          if (init == ALL_HAVOCING){
            out << "NONDETERMINISTIC ASSIGNMENTS FOR ALL FUNCTION CALLS ";
          } else {
            out << "FUNCTION SUMMARIES (for " << summaries_count << " calls) ";
          }
          out << "AREN'T SUITABLE FOR CHECKING ASSERTION." << std::endl;
          refiner.refine(*decider);

          if (refiner.get_refined_functions().size() == 0){
            out << "A real bug found." << std::endl;
            break;
          } else {
            out << "Counterexample is spurious."  << std::endl <<
                   "Got to next iteration." << std::endl;
          }
        } else if (omega.get_nondets_count() != 0) {
              // if there are still some havoced function calls, do force inlining for them
          refiner.set_refine_mode(FORCE_INLINING);
          refiner.refine(*decider);
          out << "Got to next iteration." << std::endl;
        } else {
          out << "ASSERTION(S) DO(ES)N'T HOLD AFTER INLINING."  << std::endl <<
                 "A real bug found." << std::endl;
          break;
        }
      }
    }
  }
  final = current_time();

  out << std::endl<< "Total number of steps: " << count << "." << std::endl <<
        "TOTAL TIME FOR CHECKING THIS CLAIM: "<< time2string(final - initial) << std::endl;
  return end;
}
