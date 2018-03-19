/*******************************************************************

 Module: Theory refiner

 Author: all

\*******************************************************************/
#include "theory_refiner.h"
#include "error_trace.h"
#include "solvers/smtcheck_opensmt2_cuf.h"
#include "symex_assertion_sum.h"
#include "prepare_smt_formula.h"
#include "smt_partitioning_target_equation.h"
#include "solvers/smtcheck_opensmt2_lra.h"
#include <time_stopping.h>

#define _NO_OPTIMIZATION /* Keep on to have reason of SAFE/UNSAFE result */
theory_refinert::~theory_refinert()
{
    if (decider != nullptr) delete decider;
}

void theory_refinert::initialize()
{
  decider = new smtcheck_opensmt2t_cuf(options.get_unsigned_int_option("bitwidth"),
          options.get_unsigned_int_option("type-byte-constraints"),
          "theory refiner");

  if (options.get_unsigned_int_option("random-seed")) decider->set_random_seed(options.get_unsigned_int_option("random-seed"));

#ifdef DISABLE_OPTIMIZATIONS  
  if (options.get_bool_option("dump-query"))
      decider->set_dump_query(true);

  if (options.get_bool_option("dump-pre-query"))
      decider->set_dump_pre_query(true);
  
  const std::string& dump_query_name = options.get_option("dump-query-name");
  if (dump_query_name != "")
      decider->set_dump_query_name(dump_query_name);
#endif  

  summarization_context.analyze_functions(ns);
  omega.initialize_summary_info (omega.get_summary_info(), goto_program);
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
  absolute_timet initial, final;
  initial=current_time();

  omega.set_initial_precision(assertion);
  const unsigned last_assertion_loc = omega.get_last_assertion_loc();
  const bool single_assertion_check = omega.is_single_assertion_check();
  const unsigned int unwind_bound = options.get_unsigned_int_option("unwind");

  smt_partitioning_target_equationt equation(ns, summarization_context,
      store_summaries_with_assertion);

#ifdef DISABLE_OPTIMIZATIONS
  if (options.get_bool_option("dump-SSA-tree")) {
    equation.set_dump_SSA_tree(true);
    equation.set_dump_SSA_tree_name(options.get_option("dump-query-name"));
  }
#endif

  summary_infot& summary_info = omega.get_summary_info();
  symex_assertion_sumt symex = symex_assertion_sumt(
            summarization_context, summary_info, ns, symbol_table,
            equation, message_handler, goto_program, last_assertion_loc,
            single_assertion_check, true, true, true, unwind_bound);

  //setup_unwind(symex);

  prepare_smt_formulat ssaTosmt = prepare_smt_formulat(equation, message_handler);

  bool end = symex.prepare_SSA(assertion);

  if (!end)
  {
      //Converts SSA to SMT formula
    ssaTosmt.convert_to_formula(*(dynamic_cast<smtcheck_opensmt2t *> (decider)), *(decider));

      // Decides the equation
    bool is_sat = ssaTosmt.is_satisfiable(*(dynamic_cast<smtcheck_opensmt2t *> (decider)));
    end = !is_sat;
  }

  if (end)
  {
#ifdef _NO_OPTIMIZATION
      std::string reason = unwindt::getWarningMessageForUnwondedCode(options.get_unsigned_int_option("unwind"));
      if (reason.size() > 0) status() << "\n\n(" << reason << ")" << endl;
#endif
      status() << "ASSERTION HOLDS" << endl << eom;
      report_success();
  } else {  //do refinement

      error_tracet error_trace;
      const std::string &log=options.get_option("logic");

      if (log == "qflra"){

          status() << "Checking if the error trace is spurious (for testing only) with LRA" << eom;

          smtcheck_opensmt2t_lra decider2(0, "Checking if the error trace is spurious (for testing only) with LRA");

//          error_trace.build_goto_trace_formula(equation,
//                *(dynamic_cast<smtcheck_opensmt2t *> (decider)),
//                        *(dynamic_cast<smtcheck_opensmt2t_lra *> (decider2)));
          error_trace.build_goto_trace_formula(equation, *(dynamic_cast<smtcheck_opensmt2t *> (decider)), decider2);

          std::vector<exprt>& exprs = equation.get_exprs_to_refine();
          decider2.check_ce(exprs);

      } else {

          status() << endl << "Trying to refine with CUF+BitBlast" << eom;

          std::set<int> exprs_ids;
          get_numbers(exprs_ids, options.get_option("custom"));

          bool refine_all = options.get_bool_option("force");

          std::vector<exprt>& exprs = equation.get_exprs_to_refine();
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
#ifdef _NO_OPTIMIZATION
                  std::string reason = unwindt::getWarningMessageForUnwondedCode(options.get_unsigned_int_option("unwind"));
                  if (reason.size() > 0) status() << "\n\n(" << reason << ")" << endl;
#endif
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
#ifdef _NO_OPTIMIZATION
                  std::string reason = unwindt::getWarningMessageForUnwondedCode(options.get_unsigned_int_option("unwind"));
                  if (reason.size() > 0) status() << "\n\n(" << reason << ")" << endl;
#endif
                  status() << "ASSERTION HOLDS" << eom;
                  report_success();
              }
          } else {

              status() << "(driven by iterative CE-analysis)" << endl << eom;
              unsigned bw = options.get_unsigned_int_option("bitwidth");
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
                          smtcheck_opensmt2t_cuf decider2(bw,
                                  options.get_unsigned_int_option("type-byte-constraints"),
                                  "forward checker");
                          decider2.check_ce(exprs, model, refined, weak, 0, exprs.size(), 1, 0);
                      }
                      break;
                    case 1 :
                      //   backward
                      {
                          smtcheck_opensmt2t_cuf decider2(bw,
                                  options.get_unsigned_int_option("type-byte-constraints"),
                                  "backward checker");
                          decider2.check_ce(exprs, model, refined, weak, exprs.size()-1, -1, -1, 0);
                      }
                      break;
                    case 2 :
                      //   forward with multiple refinement
                      last = 0;
                      {
                          while (last != -1 || last == exprs.size()){
                            smtcheck_opensmt2t_cuf decider2(bw,
                                    options.get_unsigned_int_option("type-byte-constraints"),
                                    "forward multiple checker");
                            last = decider2.check_ce(exprs, model, refined, weak, last, exprs.size(), 1, 0);
                          }
                      }
                      break;
                    case 3 :
                      //   backward with multiple refinement
                      last = exprs.size()-1;
                      {
                          while (last >= 0){
                            smtcheck_opensmt2t_cuf decider2(bw,
                                    options.get_unsigned_int_option("type-byte-constraints"),
                                    "backward multiple refiner");
                            last = decider2.check_ce(exprs, model, refined, weak, last, -1, -1, 0);
                          }
                      }
                      break;
                    case 4 :
                      //   forward with dependencies
                      {
                          smtcheck_opensmt2t_cuf decider2(bw,
                                  options.get_unsigned_int_option("type-byte-constraints"),
                                  "Forward dependency checker");
                          decider2.check_ce(exprs, model, refined, weak, 0, exprs.size(), 1, 1);
                      }
                      break;
                    case 5 :
                      //   backward with dependencies
                      {
                          smtcheck_opensmt2t_cuf decider2(bw,
                                  options.get_unsigned_int_option("type-byte-constraints"),
                                  "Backward dependency checker");
                          decider2.check_ce(exprs, model, refined, weak, exprs.size()-1, -1, -1, 1);
                      }
                      break;
                    case 6 :
                      //   forward with multiple refinement & dependencies
                      last = 0;
                      {
                          while (last != -1 || last == exprs.size()){
                            smtcheck_opensmt2t_cuf decider2(bw,
                                    options.get_unsigned_int_option("type-byte-constraints"),
                                    "Foward with multiple refinements & dependencies");
                            decider2.check_ce(exprs, model, refined, weak, last, exprs.size(), 1, 1);
                          }
                      }
                      break;
                    case 7 :
                      //   backward with multiple refinement & dependencies
                      last = exprs.size()-1;
                      {
                          while (last >= 0){
                            smtcheck_opensmt2t_cuf decider2(bw,
                                    options.get_unsigned_int_option("type-byte-constraints"),
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
#ifdef _NO_OPTIMIZATION
                          std::string reason = unwindt::getWarningMessageForUnwondedCode(options.get_unsigned_int_option("unwind"));
                          if (reason.size() > 0) status() << "\n\n(" << reason << ")" << endl;
#endif
                          status() << endl << "ASSERTION HOLDS" << eom;
                          report_success();
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
                      break;
                  } else {
                      status() << endl << "Naive refinement successful" << endl;
                      status() << "(" << refined.size() << " counter-examples + refine everything else)" << endl;
                      status() << "Command-line options to double-check: --theoref --custom ";
                      for (unsigned int i = 0; i < exprs.size(); i++){
                          status() << i << ",";
                      }
#ifdef _NO_OPTIMIZATION
                      std::string reason = unwindt::getWarningMessageForUnwondedCode(options.get_unsigned_int_option("unwind"));
                      if (reason.size() > 0) status() << "\n\n(" << reason << ")" << endl;
#endif
                      status() << endl << "ASSERTION HOLDS" << eom;
                      report_success();
                      break;
                  }
              }
          }
      }
  }

  final = current_time();

  status() << "TOTAL TIME FOR CHECKING THIS CLAIM: " << (final - initial) << eom;

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

///*******************************************************************\
//
//Function: theory_refinert::setup_unwind
//
//  Inputs:
//
// Outputs:
//
// Purpose: Setup the unwind bounds.
//
//\*******************************************************************/
//
//void theory_refinert::setup_unwind(symex_assertion_sumt& symex)
//{
//  const std::string &set=options.get_option("unwindset");
//  unsigned int length=set.length();
//
//  for(unsigned int idx=0; idx<length; idx++)
//  {
//    std::string::size_type next=set.find(",", idx);
//    std::string val=set.substr(idx, next-idx);
//
//    if(val.rfind(":")!=std::string::npos)
//    {
//      std::string id=val.substr(0, val.rfind(":"));
//      unsigned long uw=atol(val.substr(val.rfind(":")+1).c_str());
//      //symex.unwind_set[id]=uw; // KE: changed in cbmc 5.5
//      symex.set_unwind_thread_loop_limit(1,id,uw); //KE: No threads support, assume main is in thread 1
//    }
//
//    if(next==std::string::npos) break;
//    idx=next;
//  }
//
//  symex.set_unwind_limit(options.get_unsigned_int_option("unwind"));
//}

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
