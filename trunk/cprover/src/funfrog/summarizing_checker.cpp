/*******************************************************************

 Module: Assertion checker that extracts and uses function 
 summaries

 Author: Ondrej Sery

\*******************************************************************/

#include "summarizing_checker.h"

void summarizing_checkert::initialize()
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

  // Prepare summary_info (incapsulated in omega), start with the lazy variant,
  // i.e., all summaries are initialized as HAVOC, except those on the way
  // to the target assertion, which are marked depending on initial mode.

  omega.process_goto_locations();
  init = get_init_mode(options.get_option("init-mode"));
  omega.setup_default_precision(init);
}

/*******************************************************************

 Function: summarizing_checkert::assertion_holds

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds

\*******************************************************************/

bool summarizing_checkert::assertion_holds(const assertion_infot& assertion)
{
  fine_timet initial, final;
  initial=current_time();
  // Trivial case
  if(assertion.get_location()->guard.is_true())
  {
    out << std::endl << "ASSERTION IS TRIVIALLY TRUE" << std::endl;
    return true;
  }
  const bool no_slicing_option = options.get_bool_option("no-slicing");
  const bool assert_grouping = !options.get_bool_option("no-assert-grouping");
  omega.set_initial_precision(assertion, assert_grouping);

  partitioning_target_equationt equation(ns, summarization_context);

  summary_infot& summary_info = omega.get_summary_info();
  symex_assertion_sumt symex = symex_assertion_sumt(
            summarization_context, summary_info, ns, context,
            equation, out, goto_program, !no_slicing_option);

  setup_unwind(symex);
  symex.loop_free_check();

  refiner_assertion_sumt refiner = refiner_assertion_sumt(
              summarization_context, omega, equation,
              get_refine_mode(options.get_option("refine-mode")), out);

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

    end = (count == 1) ? symex.prepare_SSA(assertion) : symex.refine_SSA (assertion, refiner.get_refined_functions());

    if (!end){

      end = prop.assertion_holds(assertion, ns, *decider, *interpolator);
      unsigned summaries_count = omega.get_summaries_count();
      if (end && interpolator->can_interpolate())
      {
        if (summaries_count == 0)   // if none of summaries are substituted then do generate new/alternative ones
        {                           // otherwise, even generated once again, they will be weaker then existing ones
          double red_timeout = compute_reduction_timeout((double)prop.get_solving_time());
          extract_interpolants(equation, red_timeout);
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

double summarizing_checkert::compute_reduction_timeout(double solving_time)
{
  double red_timeout = 0;
  const char* red_timeout_str = options.get_option("reduce-proof").c_str();
  if (strlen(red_timeout_str)) {
    char* result;
    red_timeout = strtod(red_timeout_str, &result);

    if (result == red_timeout_str) {
            std::cerr << "WARNING: Invalid value of reduction time fraction \"" <<
                            red_timeout_str << "\". No reduction will be applied." << std::endl;
    } else {
      red_timeout = solving_time / 1000 * red_timeout;
    }
  }
  return red_timeout;
}

/*******************************************************************\

Function: summarizing_checkert::extract_interpolants

  Inputs:

 Outputs:

 Purpose: Extract and store the interpolation summaries

\*******************************************************************/

void summarizing_checkert::extract_interpolants (partitioning_target_equationt& equation, double red_timeout)
{
  summary_storet& summary_store = summarization_context.get_summary_store();
  interpolant_mapt itp_map;

  fine_timet before, after;
  before=current_time();
  equation.extract_interpolants(*interpolator, *decider, itp_map, red_timeout);
  after=current_time();
  out << "INTERPOLATION TIME: "<< time2string(after-before) << std::endl;

  for (interpolant_mapt::iterator it = itp_map.begin();
                  it != itp_map.end(); ++it) {
    summary_infot& summary_info = it->first->summary_info;

    function_infot& function_info =
            summarization_context.get_function_info(
            summary_info.get_function_id());

    function_info.add_summary(summary_store, it->second,
            !options.get_bool_option("no-summary-optimization"));

    summary_info.add_used_summary(it->second);
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
    return FORCE_INLINING;
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
