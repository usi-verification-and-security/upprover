/*******************************************************************

 Module: Assertion checker in no-partition mode
 (The code was taken from core_checker.cpp;
 TODO later investigate if summary store and omega is not needed in no_partition, please get rid of those)

 \*******************************************************************/

#include "funfrog/core_checker.h"
#include "funfrog/dependency_checker.h"
#include "funfrog/nopartition/prepare_formula_no_partition.h"
#include "funfrog/nopartition/symex_no_partition.h"
#include <langapi/language_util.h>
#include "funfrog/smt_summary_store.h"      // OpenSMT smt store

/*******************************************************************
 Function: core_checkert::assertion_holds_smt_no_partition

 Purpose: Checks if the given assertion of the GP holds for smt encoding
\*******************************************************************/
bool core_checkert::assertion_holds_smt_no_partition(
    const assertion_infot& assertion)
{
  auto before=timestamp();

  const bool no_slicing_option = options.get_bool_option(HiFrogOptions::NO_SLICING);
//  const bool no_ce_option = options.get_bool_option("no-error-trace");
//  const unsigned last_assertion_loc = omega.get_last_assertion_loc();
//  const bool single_assertion_check = omega.is_single_assertion_check();

  hifrog_symex_target_equationt equation(ns);
#ifdef DISABLE_OPTIMIZATIONS
  if (options.get_bool_option("dump-SSA-form")) {
    equation.set_dump_SSA_tree(true);
    equation.set_dump_SSA_tree_name(options.get_option("dump-query-name"));
  }
#endif
  //guard_managert guard_manager;
  std::unique_ptr<path_storaget> worklist;
  symex_no_partitiont symex {options, *worklist, ns.get_symbol_table(), equation, message_handler,
                             get_main_function() ,!no_slicing_option};
  symex.setup_unwind(options.get_unsigned_int_option(HiFrogOptions::UNWIND));


  prepare_formula_no_partitiont prop = prepare_formula_no_partitiont(
      equation, message_handler, max_memory_used);

  unsigned count = 0;
  bool end = false;
  std::cout <<"";


  while (!end)
  {
    count++;
    end = (count == 1)
          ? symex.prepare_SSA(assertion, omega.get_goto_functions())
          : symex.refine_SSA (assertion, false); // Missing sets of refined functions, TODO

    //LA: good place?
//    if(options.get_bool_option("list-templates"))
//    {
//        status() << "No listing templates option in this mode\n" << eom;
//        return true;
//    }

    if (!end){
      if (options.get_bool_option("claims-opt") && count == 1){
        dependency_checkert(ns, message_handler, get_main_function(), omega, options.get_unsigned_int_option("claims-opt"), equation.SSA_steps.size())
            .do_it(equation);
        status() << (std::string("Ignored SSA steps after dependency checker: ") + std::to_string(equation.count_ignored_SSA_steps())) << eom;
      }

      end = prop.convert_to_formula_and_solve(
          *(decider->get_convertor()), *(decider->get_solver()));
      unsigned summaries_count = omega.get_summaries_count();
      // MB: unused variable commented out
      //unsigned nondet_count = omega.get_nondets_count();
      if (end)
      {
        if (options.get_bool_option("no-itp"))
          status() << ("Skip generating interpolants") << eom;

        if (summaries_count == 0)
        {
          status() << ("ASSERTION(S) HOLD(S) ") << eom; //TODO change the message to something more clear (like, everything was inlined...)
        } else {
          status() << "FUNCTION SUMMARIES (for " << summaries_count
                   << " calls) WERE SUBSTITUTED SUCCESSFULLY." << eom;
        }
        report_success();
      } else {
        // TOOD - take care of the basic (old) refinement
        /*if (summaries_count > 0 || nondet_count > 0) {
          if (summaries_count > 0){
            status() << "FUNCTION SUMMARIES (for " << summaries_count
                   << " calls) AREN'T SUITABLE FOR CHECKING ASSERTION." << eom;
          }
          if (nondet_count > 0){
            status() << "HAVOCING (of " << nondet_count
                   << " calls) AREN'T SUITABLE FOR CHECKING ASSERTION." << eom;
          }
          refiner.refine(*(dynamic_cast <smtcheck_opensmt2t*> (decider)), omega.get_call_tree_root(), equation);

          if (refiner.get_refined_functions().size() == 0){
            assertion_violated(prop, symex.guard_expln);
            break;
          } else {
            //status("Counterexample is spurious");
            status() << ("Go to next iteration\n") << eom;
          }
        } else {*/
        assertion_violated_no_partition(prop, symex.guard_expln);
        break;
        //}
      }
    }
  }
  auto after = timestamp();
  omega.get_unwinding_depth();

  status() << "Initial unwinding bound: " << options.get_unsigned_int_option("unwind") << eom;
  status() << "Total number of steps: " << count << eom;
  if (omega.get_recursive_total() > 0){
    status() << "Unwinding depth: " <<  omega.get_recursive_max() << " (" << omega.get_recursive_total() << ")" << eom;
  }
  status() << "TOTAL TIME FOR CHECKING THIS CLAIM: " << time_gap(after, before) << eom;

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

  return end;
}
/*******************************************************************
 Function: core_checkert::assertion_violated

 Purpose: Prints the error trace for smt encoding
\*******************************************************************/
void core_checkert::assertion_violated_no_partition(prepare_formula_no_partitiont &prop,
                                                    std::map<irep_idt, std::string> &guard_expln)
{
  if (!options.get_bool_option("no-error-trace")) {
    auto solver = decider->get_solver();
    assert(solver);
    prop.error_trace(*decider, ns, guard_expln);
    if (solver->is_overapprox_encoding()) {
      status() << "\nA bug found." << "\n";
      status() << "WARNING: Possibly due to the Theory conversion." << eom;
    } else {
      status() << "A real bug found." << eom;
    }
  }
  report_failure();
}
