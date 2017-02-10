/*******************************************************************

 Module: Theory refiner

 Author: all

\*******************************************************************/
#include "theory_refiner.h"
#include "error_trace.h"
#include "solvers/smtcheck_opensmt2_lra.h"

void theory_refinert::initialize()
{
  decider = new smtcheck_opensmt2t_cuf(options.get_unsigned_int_option("bitwidth"));
  summarization_context.analyze_functions(ns);
  omega.initialize_summary_info (omega.get_summary_info(), goto_program);
  omega.setup_default_precision(ALL_SUBSTITUTING);
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

  std::vector<unsigned> ints;

  smt_partitioning_target_equationt equation(ns, summarization_context, false,
      store_summaries_with_assertion, NO_COLORING, ints);

  summary_infot& summary_info = omega.get_summary_info();
  symex_assertion_sumt symex = symex_assertion_sumt(
            summarization_context, summary_info, ns, symbol_table,
            equation, message_handler, goto_program, last_assertion_loc,
            single_assertion_check, true, true, true);

  setup_unwind(symex);

  smt_assertion_sumt prop = smt_assertion_sumt(summarization_context,
          equation, message_handler, max_memory_used);

  bool end = symex.prepare_SSA(assertion);

  if (!end) end = prop.assertion_holds(assertion, ns,
          *(dynamic_cast<smtcheck_opensmt2t *> (decider)),
          *(dynamic_cast<interpolating_solvert *> (decider)));

  if (end)
  {
      status() << "ASSERTION HOLDS" << endl << eom;
      report_success();
  } else {

      error_tracet error_trace;
      const std::string &log=options.get_option("logic");

      if (log == "qflra"){

          status() << "Checking if the error trace is spurious (for testing only) with LRA" << eom;

          smtcheck_opensmt2t_lra* decider2 = new smtcheck_opensmt2t_lra(0);

          error_trace.build_goto_trace_formula(equation,
                *(dynamic_cast<smtcheck_opensmt2t *> (decider)),
                        *(dynamic_cast<smtcheck_opensmt2t_lra *> (decider2)));

          std::vector<exprt>& exprs = equation.get_exprs_to_refine();
          decider2->check_ce(exprs);

      } else {

          status() << endl << "Trying to refine with CUF+BitBlast" << endl;

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
                  report_failure();
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
                  status() << "ASSERTION DOES NOT HOLD" << eom;
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

              while (true){

                  // local CUF solver
                  smtcheck_opensmt2t_cuf* decider2 =
                          new smtcheck_opensmt2t_cuf(options.get_unsigned_int_option("bitwidth"));

                  std::map<const exprt, int> model;

                  error_trace.build_goto_trace_formula(exprs, model,
                        *(dynamic_cast<smtcheck_opensmt2t *> (decider)));

                  std::set<int> weak;
                  decider2->check_ce(exprs, model, refined, weak);

                  if (weak.size() > 0){
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
                          break;
                      }
                  } else /* if (decider->force_refine_ce(exprs, refined) )*/{ // TODO: uncomment
                      status() << endl << "Obtained counter-examples are refined" << endl;
                      status() << "(" << refined.size() << " / "
                                      << exprs.size()  << " expressions bit-blasted)" << endl;
                      status() << "ASSERTION DOES NOT HOLD" << eom;
                      report_failure();
                      break;
                 /* } else {
                      status() << endl << "Naive refinement successful" << endl;
                      status() << "(" << iter << " counter-examples + refine everything else)" << endl;
                      status() << "ASSERTION HOLDS" << eom;
                      report_success();
                      break; */
                  }
              }
          }
      }
  }

  final = current_time();

  status() << "TOTAL TIME FOR CHECKING THIS CLAIM: " << (final - initial) << eom;
  return end;
}

/*******************************************************************\

Function: theory_refinert::setup_unwind

  Inputs:

 Outputs:

 Purpose: Setup the unwind bounds.

\*******************************************************************/

void theory_refinert::setup_unwind(symex_assertion_sumt& symex)
{
  const std::string &set=options.get_option("unwindset");
  unsigned int length=set.length();

  for(unsigned int idx=0; idx<length; idx++)
  {
    std::string::size_type next=set.find(",", idx);
    std::string val=set.substr(idx, next-idx);

    if(val.rfind(":")!=std::string::npos)
    {
      std::string id=val.substr(0, val.rfind(":"));
      unsigned long uw=atol(val.substr(val.rfind(":")+1).c_str());
      //symex.unwind_set[id]=uw; // KE: changed in cbmc 5.5
      symex.set_unwind_thread_loop_limit(1,id,uw); //KE: No threads support, assume main is in thread 1
    }
    
    if(next==std::string::npos) break;
    idx=next;
  }

  symex.set_unwind_limit(options.get_unsigned_int_option("unwind"));
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
  
  case ui_message_handlert::PLAIN:
    std::cout << std::endl << std::endl << "VERIFICATION SUCCESSFUL" << std::endl;
    break;

  case ui_message_handlert::XML_UI:
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

  case ui_message_handlert::PLAIN:
    std::cout << std::endl << std::endl << "VERIFICATION FAILED" << std::endl;
    break;

  case ui_message_handlert::XML_UI:
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
