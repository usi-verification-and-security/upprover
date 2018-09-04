/*******************************************************************

 Module: Theory refiner

 Author: all

\*******************************************************************/
#include "theory_refiner.h"
#include "error_trace.h"
#include "solvers/smtcheck_opensmt2_cuf.h"
#include "symex_assertion_sum.h"
#include "prepare_formula.h"
#include "partitioning_target_equation.h"
#include "solvers/smtcheck_opensmt2_lra.h"
#include "smt_summary_store.h"
#include "assertion_info.h"
#include "utils/time_utils.h"
#include <langapi/language_util.h>
#include "partitioning_slice.h"

#define _NO_OPTIMIZATION /* Keep on to have reason of SAFE/UNSAFE result */
theory_refinert::~theory_refinert()
{
    if (decider != nullptr) delete decider;
}

void theory_refinert::initialize()
{
    // Extend once adding interpolation for mix theories
    solver_options.initialize_mix_encoding_solver_options(
          options.get_unsigned_int_option("type-byte-constraints"),
          options.get_unsigned_int_option("bitwidth"));
    solver_options.m_verbosity = options.get_unsigned_int_option("verbose-solver");
  
    if(options.get_unsigned_int_option("random-seed")) 
        solver_options.m_random_seed = options.get_unsigned_int_option("random-seed");
  
  decider = new smtcheck_opensmt2t_cuf(solver_options, "theory refiner");

  omega.initialize_summary_info (omega.get_call_tree_root(), goto_program);
  omega.setup_default_precision(init_modet::ALL_SUBSTITUTING);
}

void get_numbers(std::set<int>& nums, std::string set){

  int length=set.length();

  for(int idx=0; idx<length; idx++)
  {
    std::string::size_type next=set.find(",", idx);
    std::string val=set.substr(idx, next-idx);
    nums.insert(stoi(val));

    if(next==std::string::npos) break;
    idx=next;
  }
}


/*******************************************************************

 Function: theory_refinert::assertion_holds_smt

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion holds in CUF with bit-blasting (when needed)

\*******************************************************************/

bool theory_refinert::assertion_holds_smt(const assertion_infot& assertion,
        bool store_summaries_with_assertion)
{
  auto before=timestamp();

  omega.set_initial_precision(assertion, [](const std::string & s) { return false; });
  const unsigned last_assertion_loc = omega.get_last_assertion_loc();
  const bool single_assertion_check = omega.is_single_assertion_check();
  const unsigned int unwind_bound = options.get_unsigned_int_option(HiFrogOptions::UNWIND);

  smt_summary_storet dummy;
  partitioning_target_equationt equation(ns, dummy,
      store_summaries_with_assertion);

#ifdef DISABLE_OPTIMIZATIONS
  if (options.get_bool_option("dump-SSA-tree")) {
    equation.set_dump_SSA_tree(true);
    equation.set_dump_SSA_tree_name(options.get_option("dump-query-name"));
  }
#endif

  call_tree_nodet& summary_info = omega.get_call_tree_root();
  std::unique_ptr<path_storaget> worklist;
  symex_assertion_sumt symex{
          omega.get_goto_functions(), summary_info, options, *worklist, ns.get_symbol_table(),
          equation, message_handler, goto_program, last_assertion_loc,
          single_assertion_check, true, unwind_bound, false};
  symex.set_assertion_info_to_verify(&assertion);

  prepare_formulat ssaTosmt = prepare_formulat(equation, message_handler);

  bool end = symex.prepare_SSA();

  if (!end)
  {
    slice_target(symex.get_target_equation());
      //Converts SSA to SMT formula
    ssaTosmt.convert_to_formula(*(dynamic_cast<smtcheck_opensmt2t *> (decider)), *(decider));

      // Decides the equation
    bool is_sat = ssaTosmt.is_satisfiable(*(dynamic_cast<smtcheck_opensmt2t *> (decider)));
    end = !is_sat;
  }

  if (end)
  {
      status() << "ASSERTION HOLDS" << endl << eom;
      report_success();

  } else {  //do refinement

      error_tracet error_trace;
      const std::string &log=options.get_option("logic");

      if (log == "qflra"){

          status() << "Checking if the error trace is spurious (for testing only) with LRA" << eom;

          smtcheck_opensmt2t_lra decider2(solver_options, "Checking if the error trace is spurious (for testing only) with LRA"
          );

//          error_trace.build_goto_trace_formula(equation,
//                *(dynamic_cast<smtcheck_opensmt2t *> (decider)),
//                        *(dynamic_cast<smtcheck_opensmt2t_lra *> (decider2)));
          error_trace.build_goto_trace_formula(equation, *(dynamic_cast<smtcheck_opensmt2t *> (decider)), decider2);

          std::vector<exprt> exprs = equation.get_exprs_to_refine();
          decider2.check_ce(exprs);

      } else {

          status() << endl << "Trying to refine with CUF+BitBlast" << eom;

          std::set<int> exprs_ids;
          get_numbers(exprs_ids, options.get_option("custom"));

          bool refine_all = options.get_bool_option("force");

          std::vector<exprt> exprs = equation.get_exprs_to_refine();
          std::set<int> refined;

          if (exprs_ids.size() > 0){

              status() << "(user-specified statements only)" << endl << eom;

              if (decider->refine_ce_mul(exprs, exprs_ids)){
                  status() << "ASSERTION UNKNOWN" << endl;
                  status() << "(further refinement needed)" << eom;
                  //report_failure(); // KE: confusing, it is UNKNOWN and SAT at the same time?!
              } else {
                  status() << endl << "Custom refinement successful" << endl;
                  status() << "(" << exprs_ids.size() << " / "
                                  << exprs.size()  << " expressions bit-blasted)" << endl;
                  status() << "ASSERTION HOLDS" << eom;
                  report_success();
              }
          } else if (refine_all) {

              status() << "(all statements at once)" << endl << eom;

              if (decider->force_refine_ce(exprs, refined)){
#ifdef _NO_OPTIMIZATION
                  std::string reason = decider->get_refinement_failure_reason();
                  if (reason.size() > 0)
                  {
                      status() << "ASSERTION UNKNOWN" << endl;
                      status() << "(further refinement needed)" << eom;
                      status() << "\n\n(" << reason << ")" << endl;
                  } else {
                      status() << "ASSERTION DOES NOT HOLD" << eom;
                  }
#endif
                  report_failure();
              } else {
                  status() << endl << "Naive refinement successful" << endl;
                  status() << "(" << exprs.size() << " / "
                                  << exprs.size()  << " expressions bit-blasted)" << endl;
                  status() << "ASSERTION HOLDS" << eom;
                  report_success();
              }
          } else {

              status() << "(driven by iterative CE-analysis)" << endl << eom;
              unsigned heuristic = options.get_unsigned_int_option("heuristic");

              while (true){

                  std::map<const exprt, int> model;

                  error_trace.build_goto_trace_formula(exprs, model,
                        *(dynamic_cast<smtcheck_opensmt2t *> (decider)));

                  std::set<int> weak;
                  int last; // compared with -1, must be signed

                  switch(heuristic) {
                    case 0 :
                      //   forward
                      {
                          smtcheck_opensmt2t_cuf decider2(solver_options, "forward checker");
                          decider2.check_ce(exprs, model, refined, weak, 0, exprs.size(), 1, 0);
                      }
                      break;
                    case 1 :
                      //   backward
                      {
                          smtcheck_opensmt2t_cuf decider2(solver_options, "backward checker");
                          decider2.check_ce(exprs, model, refined, weak, exprs.size()-1, -1, -1, 0);
                      }
                      break;
                    case 2 :
                      //   forward with multiple refinement
                      last = 0;
                      {
                          while (last != -1 || last == (int) exprs.size()){
                            smtcheck_opensmt2t_cuf decider2(solver_options, "forward multiple checker");
                            last = decider2.check_ce(exprs, model, refined, weak, last, exprs.size(), 1, 0);
                          }
                      }
                      break;
                    case 3 :
                      //   backward with multiple refinement
                      last = exprs.size()-1;
                      {
                          while (last >= 0){
                            smtcheck_opensmt2t_cuf decider2(solver_options, "backward multiple refiner");
                            last = decider2.check_ce(exprs, model, refined, weak, last, -1, -1, 0);
                          }
                      }
                      break;
                    case 4 :
                      //   forward with dependencies
                      {
                          smtcheck_opensmt2t_cuf decider2(solver_options, "Forward dependency checker");
                          decider2.check_ce(exprs, model, refined, weak, 0, exprs.size(), 1, 1);
                      }
                      break;
                    case 5 :
                      //   backward with dependencies
                      {
                          smtcheck_opensmt2t_cuf decider2(solver_options, "Backward dependency checker");
                          decider2.check_ce(exprs, model, refined, weak, exprs.size()-1, -1, -1, 1);
                      }
                      break;
                    case 6 :
                      //   forward with multiple refinement & dependencies
                      last = 0;
                      {
                          while (last != -1 || last == (int) exprs.size()){
                            smtcheck_opensmt2t_cuf decider2(solver_options, "Foward with multiple refinements & dependencies");
                            decider2.check_ce(exprs, model, refined, weak, last, exprs.size(), 1, 1);
                          }
                      }
                      break;
                    case 7 :
                      //   backward with multiple refinement & dependencies
                      last = exprs.size()-1;
                      {
                          while (last >= 0){
                            smtcheck_opensmt2t_cuf decider2(solver_options, 
                                    "backward with multiple refinement & dependencies");
                            decider2.check_ce(exprs, model, refined, weak, last, -1, -1, 1);
                          }
                      }
                      break;
                  }

                  if (weak.size() > 0){

                      status() << "  Weak statement encodings (" << weak.size() << ") found" << endl;

                      for (auto it = weak.begin(); it != weak.end(); ++it){
                          refined.insert(*it);
                      }

                      if (!decider->refine_ce_mul(exprs, weak)){
                          status() << endl << "Refinement successful" << endl;
                          status() << "(" << refined.size() << " / "
                                          << exprs.size()  << " expressions bit-blasted)" << endl;
                          status() << "Command-line options to double-check: --theoref --custom ";
                          for (auto it = refined.begin(); it != refined.end(); ++it){
                              status() << *it << ",";
                          }
                          status() << endl << "ASSERTION HOLDS" << eom;
                          report_success();
                          end = true;
                          break;
                      }
                  } else  if (decider->force_refine_ce(exprs, refined) ){ // TODO: comment once the bug with thoref is fixed
                      status() << endl << "Obtained counter-examples are refined" << endl;
                      status() << "(" << refined.size() << " / "
                                      << exprs.size()  << " expressions bit-blasted)" << endl;
#ifdef _NO_OPTIMIZATION
                      std::string reason = decider->get_refinement_failure_reason();
                      if (reason.size() > 0)
                      {
                        status() << "ASSERTION UNKNOWN" << endl;
                        status() << "(further refinement needed)" << eom;
                        status() << "\n\n(" << reason << ")" << endl;
                      } else {
                        status() << "ASSERTION DOES NOT HOLD" << eom;
                      }
#endif
                      report_failure();
                      end = false;
                      break;
                  } else {
                      status() << endl << "Naive refinement successful" << endl;
                      status() << "(" << refined.size() << " counter-examples + refine everything else)" << endl;
                      status() << "Command-line options to double-check: --theoref --custom ";
                      for (unsigned int i = 0; i < exprs.size(); i++){
                          status() << i << ",";
                      }
                      status() << endl << "ASSERTION HOLDS" << eom;
                      report_success();
                      end = true;
                      break;
                  }
              }
          }
      }
  }

  auto after = timestamp();

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

  return end;
}


/*******************************************************************\

Function: theory_refinert::report_success

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void theory_refinert::report_success()
{
  //status() << ("VERIFICATION SUCCESSFUL");

  switch(message_handler.get_ui())
  {
  
    case ui_message_handlert::uit::PLAIN:
    result() << "\n\nVERIFICATION SUCCESSFUL" << eom;
    break;

    case ui_message_handlert::uit::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="SUCCESS";
      std::cout << xml;
      std::cout << std::endl;
    }
    break;

  default:
    assert(false);
  }
}

void theory_refinert::slice_target(partitioning_target_equationt & equation) {
    auto before = timestamp();
    statistics() << "All SSA steps: " << equation.SSA_steps.size() << eom;
    partitioning_slice(equation);
    statistics() << "Ignored SSA steps after slice: " << equation.count_ignored_SSA_steps() << eom;
    auto after = timestamp();
    statistics() << "SLICER TIME: " << time_gap(after,before) << eom;
}

/*******************************************************************\

Function: theory_refinert::report_failure

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void theory_refinert::report_failure()
{
  switch(message_handler.get_ui())
  {

  case ui_message_handlert::uit::PLAIN:
    result() << "\n\nVERIFICATION FAILED" << eom;
    break;

  case ui_message_handlert::uit::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="FAILURE";
      std::cout << xml;
      std::cout << std::endl;
    }
    break;

  default:
    assert(false);
  }
}
