/*******************************************************************

 Module: Assertion checker that extracts and uses function 
 summaries

 Author: Ondrej Sery

\*******************************************************************/

#include "summarizing_checker.h"

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
  // to the target assertion, which are marked INLINE.
  summary_infot summary_info;
  summary_info.initialize(summarization_context, goto_program, assertion);


  summarization_context.enable_refinement = false;
            //FIXME: options.get_int_option("enable-refinement"); - with different types of refinement available
  summarization_context.force_inlining = false;
            //FIXME: move force_inlining to the refinement schema
  unsigned count = 0;
  bool end = false;
  while (!end && count < 5) // FIXME: hardcoded (for a while) limit of refinement tries
  {
    bv_pointerst *deciderp = new bv_pointerst(ns, *opensmt);
    deciderp->unbounded_array = bv_pointerst::U_AUTO;
    decider.reset(deciderp);
    interpolator.reset(opensmt);
    opensmt->reset_solver();

    partitioning_target_equationt equation(ns);

    // FIXME: move constructor, setup_unwind, and loop_free_check away from the loop
    symex_assertion_sumt symex = symex_assertion_sumt(
              summarization_context, summary_info, ns, context,
              equation, out, goto_program, !no_slicing_option);

    setup_unwind(symex);
    symex.loop_free_check();

    end = symex.prepare_SSA(assertion);

    if (!end){

      refiner_assertion_sumt refiner = refiner_assertion_sumt(
                  summarization_context, equation, out);
      end = refiner.refine();

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
        } else if (count == 0 && symex.sum_count != 0){
          out << "FUNCTION SUMMARIES (for " << symex.sum_count << 
                  " calls) AREN'T SUITABLE FOR CHECKING ASSERTION." << std::endl <<
                  "Try to inline everything then." << std::endl;
        } else if (symex.sum_count == 0){
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


void summarizing_checkert::extract_interpolants (partitioning_target_equationt& equation, double red_timeout)
{
  interpolant_mapt itp_map;

  fine_timet before, after;
  before=current_time();
  equation.extract_interpolants(*interpolator, *decider, itp_map, red_timeout);
  after=current_time();
  out << "INTERPOLATION TIME: "<< time2string(after-before) << std::endl;
  // Extract the interpolation summaries here...
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
