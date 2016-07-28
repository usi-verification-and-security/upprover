/*******************************************************************

 Module: Assertion checker that extracts and uses function 
 summaries

 Author: Ondrej Sery

\*******************************************************************/
#include <i2string.h>
#include "summarizing_checker.h"
#include "partitioning_slice.h"
//#include "dependency_checker.h"

void summarizing_checkert::initialize()
{
  decider = new smtcheck_opensmt2t();
  // Prepare the summarization context
  summarization_context.analyze_functions(ns);

  // Load older summaries
  {
    const std::string& summary_file = options.get_option("load-summaries");
    if (!summary_file.empty()) {
      summarization_context.deserialize_infos(summary_file, decider);
    }
  }

  // Prepare summary_info (encapsulated in omega), start with the lazy variant,
  // i.e., all summaries are initialized as HAVOC, except those on the way
  // to the target assertion, which are marked depending on initial mode.

  omega.initialize_summary_info (omega.get_summary_info(), goto_program);
  //omega.process_goto_locations();
  init = get_init_mode(options.get_option("init-mode"));
  omega.setup_default_precision(init);
}

void get_ints(std::vector<unsigned>& claims, std::string set){

  unsigned int length=set.length();

  for(unsigned idx=0; idx<length; idx++)
  {
    std::string::size_type next=set.find(",", idx);
    std::string val=set.substr(idx, next-idx);
    claims.push_back(atoi(val.c_str()));

    if(next==std::string::npos) break;
    idx=next;
  }
}

/*******************************************************************

 Function: summarizing_checkert::assertion_holds

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds

\*******************************************************************/

bool summarizing_checkert::assertion_holds(const assertion_infot& assertion,
        bool store_summaries_with_assertion)
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

  omega.set_initial_precision(assertion);
  const unsigned last_assertion_loc = omega.get_last_assertion_loc();
  const bool single_assertion_check = omega.is_single_assertion_check();

  std::vector<unsigned> ints;
  get_ints(ints, options.get_option("part-itp"));

  partitioning_target_equationt equation(ns, summarization_context, false,
      store_summaries_with_assertion, get_coloring_mode(options.get_option("color-proof")), ints);

  summary_infot& summary_info = omega.get_summary_info();
  symex_assertion_sumt symex = symex_assertion_sumt(
            summarization_context, summary_info, ns, symbol_table,
            equation, message_handler, goto_program, last_assertion_loc,
            single_assertion_check, !no_slicing_option);

  setup_unwind(symex);

  refiner_assertion_sumt refiner = refiner_assertion_sumt(
              summarization_context, omega, equation,
              get_refine_mode(options.get_option("refine-mode")),
              message_handler, last_assertion_loc, true);

  prop_assertion_sumt prop = prop_assertion_sumt(summarization_context,
          equation, message_handler, max_memory_used);
  unsigned count = 0;
  bool end = false;
  if(&message_handler!=NULL){
	  std::cout <<"";
  }

  while (!end)
  {
    count++;

    //decider = new smtcheck_opensmt2t();

//    interpolator.reset(opensmt);
//    bv_pointerst *deciderp = new bv_pointerst(ns, *opensmt);
//    deciderp->unbounded_array = bv_pointerst::U_AUTO;
//    decider.reset(deciderp);

    end = (count == 1) ? symex.prepare_SSA(assertion) : symex.refine_SSA (assertion, refiner.get_refined_functions());

    if (!end){

      end = prop.assertion_holds(assertion, ns, *decider, *decider);
      unsigned summaries_count = omega.get_summaries_count();
      unsigned nondet_count = omega.get_nondets_count();
      if (end && decider->can_interpolate())
      {
        if (options.get_bool_option("no-itp")){
          status("Skip generating interpolants");
        } else {
          status("Start generating interpolants...");
          extract_interpolants(prop, equation);
        }
        if (summaries_count == 0)
        {
          status("ASSERTION(S) HOLD(S)"); //TODO change the message to something more clear (like, everything was inlined...)
        } else {
          status() << "FUNCTION SUMMARIES (for " << summaries_count
        	   << " calls) WERE SUBSTITUTED SUCCESSFULLY." << eom;
        }
        report_success();
      } else {
        if (summaries_count > 0 || nondet_count > 0) {
          if (summaries_count > 0){
            status() << "FUNCTION SUMMARIES (for " << summaries_count
                   << " calls) AREN'T SUITABLE FOR CHECKING ASSERTION." << eom;
          }
          if (nondet_count > 0){
            status() << "HAVOCING (of " << nondet_count
                   << " calls) AREN'T SUITABLE FOR CHECKING ASSERTION." << eom;
          }
          refiner.refine(*decider, omega.get_summary_info());

          if (refiner.get_refined_functions().size() == 0){
            prop.error_trace(*decider, ns);
            status("A real bug found.");
            report_failure();
            break;
          } else {
            //status("Counterexample is spurious");
            status("Go to next iteration");
          }
        } else {
          prop.error_trace(*decider, ns);
          status("ASSERTION(S) DO(ES)N'T HOLD");
          status("A real bug found");
          report_failure();
          break;
        }
      }
    }
  }
  final = current_time();
  omega.get_unwinding_depth();

  status() << "Initial unwinding bound: " << options.get_int_option("unwind") << eom;
  status() << "Total number of steps: " << count << eom;
  if (omega.get_recursive_total() > 0){
    status() << "Unwinding depth: " <<  omega.get_recursive_max() << " (" << omega.get_recursive_total() << ")" << eom;
  }
  status() << "TOTAL TIME FOR CHECKING THIS CLAIM: " << (final - initial) << eom;
  return end;
}

/*******************************************************************\

Function: summarizing_checkert::extract_interpolants

  Inputs:

 Outputs:

 Purpose: Extract and store the interpolation summaries

\*******************************************************************/

void summarizing_checkert::extract_interpolants (prop_assertion_sumt& prop, partitioning_target_equationt& equation)
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
    summary_info.set_summary();           // helpful flag for omega's (de)serialization
  }
  // Store the summaries
  const std::string& summary_file = options.get_option("save-summaries");
  if (!summary_file.empty()) {
    summarization_context.serialize_infos(summary_file, 
            omega.get_summary_info());
  }
}
/*******************************************************************\

Function: summarizing_checkert::setup_unwind

  Inputs:

 Outputs:

 Purpose: Setup the unwind bounds.

\*******************************************************************/

void summarizing_checkert::setup_unwind(symex_assertion_sumt& symex)
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
      symex.unwind_set[id]=uw;
    }
    
    if(next==std::string::npos) break;
    idx=next;
  }

  symex.max_unwind=options.get_int_option("unwind");
}

/*******************************************************************\

Function: get_refine_mode

  Inputs:

 Outputs:

 Purpose: Determining the refinement mode from a string.

\*******************************************************************/

refinement_modet get_refine_mode(const std::string& str)
{
  if (str == "force-inlining" || str == "0"){
    return FORCE_INLINING;
  } else if (str == "random-substitution" || str == "1"){
    return RANDOM_SUBSTITUTION;
  } else if (str == "slicing-result" || str == "2"){
    return SLICING_RESULT;
  } else {
    // by default
    return SLICING_RESULT;
  }
};

/*******************************************************************\

Function: get_initial_mode

  Inputs:

 Outputs:

 Purpose: Determining the initial mode from a string.

\*******************************************************************/

init_modet get_init_mode(const std::string& str)
{
  if (str == "havoc-all" || str == "0"){
    return ALL_HAVOCING;
  } else if (str == "use-summaries" || str == "1"){
    return ALL_SUBSTITUTING;
  } else {
    // by default
    return ALL_SUBSTITUTING;
  }
};


coloring_modet get_coloring_mode(const std::string& str)
{
  if (str == "0"){
    return RANDOM_COLORING;
  } else if (str == "1"){
    return COLORING_FROM_FILE;
  } else {
    // by default
    return NO_COLORING;
  }
};

/*******************************************************************\

Function: summarizing_checkert::report_success

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizing_checkert::report_success()
{
  //status("VERIFICATION SUCCESSFUL");

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

Function: summarizing_checkert::report_failure

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizing_checkert::report_failure()
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
