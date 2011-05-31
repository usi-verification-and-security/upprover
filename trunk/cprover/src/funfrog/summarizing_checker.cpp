/*******************************************************************

 Module: Assertion checker that extracts and uses function 
 summaries

 Author: Ondrej Sery

\*******************************************************************/

#include "summarizing_checker.h"

void summarizing_checkert::initialize()
{
  opensmt = new satcheck_opensmtt(
      options.get_int_option("verbose-solver"),
      options.get_bool_option("save-queries"));

  // Prepare the summarization context
  summarization_context.analyze_functions(ns);

  // Load older summaries
  {
    const std::string& summary_file = options.get_option("load-summaries");
    if (!summary_file.empty()) {
      summarization_context.deserialize_infos(summary_file);
    }
  }
  // Prepare summary_info, start with the lazy variant, i.e.,
  // all summaries are initialized as NONDET except those on the way
  // to the target assertion, which are marked depending on initial mode.
  summary_info.initialize(summarization_context, goto_program);
  if (true){
    summary_info.process_goto_locations();
  }
  init = get_init_mode(options.get_option("init-mode"));
  summary_infot::setup_default_precision(init);
}

/*******************************************************************

 Function: summarizing_checkert::assertion_holds

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds

\*******************************************************************/

bool summarizing_checkert::assertion_holds(const assertion_infot& assertion)
{
  // Trivial case
  if(assertion.get_location()->guard.is_true())
  {
    out << std::endl << "ASSERTION IS TRIVIALLY TRUE" << std::endl;
    return true;
  }

  const bool no_slicing_option = options.get_bool_option("no-slicing");
  summary_info.set_initial_precision(summarization_context, assertion);

  unsigned count = 0;
  bool end = false;
  while (!end && count < (unsigned)options.get_int_option("steps"))
  {
    bv_pointerst *deciderp = new bv_pointerst(ns, *opensmt);
    deciderp->unbounded_array = bv_pointerst::U_AUTO;
    decider.reset(deciderp);
    interpolator.reset(opensmt);
    opensmt->reset_solver();

    partitioning_target_equationt equation(ns);

    // FIXME: move constructor, setup_unwind, and loop_free_check
    //        (as well as constructors for equation, prop, refiner)
    //        away from the loop

    symex_assertion_sumt symex = symex_assertion_sumt(
              summarization_context, summary_info, ns, context,
              equation, out, goto_program, !no_slicing_option);

    setup_unwind(symex);
    symex.loop_free_check();

    end = symex.prepare_SSA(assertion);

    if (!end){

      prop_assertion_sumt prop = prop_assertion_sumt(
            *decider, *interpolator, equation, out, max_memory_used);
      end = prop.assertion_holds(assertion, ns);

      if (end && interpolator->can_interpolate())
      {
        if (symex.sum_count == 0)   // if none of summaries are substituted then do generate new/alternative ones
        {                           // otherwise, even generated once again, they will be weaker then existing ones
          double red_timeout = compute_reduction_timeout((double)prop.get_solving_time());
          extract_interpolants(equation, red_timeout);
          out << "ASSERTION(S) HOLD(S) AFTER INLINING." << std::endl;
        } else {
          out << "FUNCTION SUMMARIES (for " << symex.sum_count << 
                  " calls) WERE SUBSTITUTED SUCCESSFULLY." << std::endl;
        }
      } else {
        if (symex.sum_count != 0 || init == ALL_HAVOCING) {
          if (init == ALL_HAVOCING){
            // FIXME: refiner then works correct. next iteration step also works correct until we store interpolants:
            //        funfrog: sat/cnf.cpp:673: bool cnft::process_clause(const bvt&, bvt&): Assertion `l.var_no()!=0' failed.
            out << "NONDETERMINISTIC ASSIGNMENTS FOR ALL FUNCTION CALLS ";
          } else {
            out << "FUNCTION SUMMARIES (for " << symex.sum_count << " calls) ";
          }
          out << "AREN'T SUITABLE FOR CHECKING ASSERTION." << std::endl <<
              "Try to refine then." << std::endl;

          refiner_assertion_sumt refiner = refiner_assertion_sumt(
                      summarization_context, summary_info, equation,
                      get_refine_mode(options.get_option("refine-mode")),
                      options.get_bool_option("havoc-unimportant"), out);
          refiner.refine();

        } else {
          out << "ASSERTION(S) DO(ES)N'T HOLD AFTER INLINING."  << std::endl <<
                  "A real bug found." << std::endl;
          break;
        }
      }
    }
    count++;
  }
  out << std::endl<< "Total number of steps: " << count << ".";
  return end;
}

/*******************************************************************\

Function: summarizing_checkert::compute_reduction_timeout

  Inputs:

 Outputs:

 Purpose: Compute reduction timeout

\*******************************************************************/

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
  interpolant_mapt itp_map;

  fine_timet before, after;
  before=current_time();
  equation.extract_interpolants(*interpolator, *decider, itp_map, red_timeout);
  after=current_time();
  out << "INTERPOLATION TIME: "<< time2string(after-before) << std::endl;

  for (interpolant_mapt::iterator it = itp_map.begin();
                  it != itp_map.end(); ++it) {
    irep_idt& function_id = it->first;
    if (!it->second.is_trivial()) {
          summarization_context.get_function_info(function_id).add_summary(it->second,
                                                          !options.get_bool_option("no-summary-optimization"));
    }
  }
  // Store the summaries
  const std::string& summary_file = options.get_option("save-summaries");
  if (!summary_file.empty()) {
    summarization_context.serialize_infos(summary_file);
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
