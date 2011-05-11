/*******************************************************************

 Module: Assertion checker that extracts and uses function 
 summaries

 Author: Ondrej Sery

\*******************************************************************/

#include <memory>

#include <goto-symex/build_goto_trace.h>
#include <find_symbols.h>
#include <ansi-c/expr2c.h>
#include <time_stopping.h>
#include <pointer-analysis/value_set_analysis.h>
#include <solvers/sat/satcheck.h>
#include <solvers/smt1/smt1_dec.h>
#include <loopfrog/memstat.h>

#include "summarizing_checker.h"
#include "summary_info.h"
#include "symex_assertion_sum.h"

#include "solvers/satcheck_opensmt.h"

/*******************************************************************

 Function: last_assertion_holds

 Inputs:

 Outputs:

 Purpose: Checks if the last assertion of the GP holds. This is only
 a convenience wrapper.

\*******************************************************************/

bool last_assertion_holds_sum(
  const contextt &context,
  const value_setst &value_sets,
  goto_programt::const_targett &head,
  const goto_programt &goto_program,
  const goto_functionst &goto_functions,
  std::ostream &out,
  unsigned long &max_memory_used,
  const optionst& options,
  bool use_smt)
{
  contextt temp_context;
  namespacet ns(context, temp_context);
  summarizing_checkert sum_checker(value_sets, head,
          goto_functions, loopstoret(), loopstoret(), ns, temp_context);

  return sum_checker.last_assertion_holds(goto_program, out,
                                    max_memory_used, options, use_smt);
}

/*******************************************************************

 Function: summarizing_checkert::last_assertion_holds

 Inputs:

 Outputs:

 Purpose: Checks if the last assertion of the GP holds. This is only
 a convenience wrapper.

\*******************************************************************/

bool summarizing_checkert::last_assertion_holds(
  const goto_programt &goto_program,
  std::ostream &out,
  unsigned long &max_memory_used,
  const optionst& options,
  bool use_smt)
{
  assert(!goto_program.empty() &&
         goto_program.instructions.rbegin()->type==ASSERT);

  goto_programt::const_targett last=goto_program.instructions.end(); last--;
  call_stackt empty_stack;
  assertion_infot assertion(empty_stack, last);

  return assertion_holds(goto_program, assertion, 
          out, max_memory_used, options, use_smt);
}

/*******************************************************************

 Function: assertion_holds_sum

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds (without 
 value sets). This is only a convenience wrapper.

\*******************************************************************/

bool assertion_holds_sum(
  const contextt &context,
  const goto_programt &goto_program,
  const goto_functionst &goto_functions,
  const assertion_infot& assertion,
  std::ostream &out,
  unsigned long &max_memory_used,
  const optionst& options,
  bool use_smt)
{
  contextt temp_context;
  namespacet ns(context, temp_context);
  goto_programt::const_targett first = goto_program.instructions.begin();
  summarizing_checkert sum_checker(value_set_analysist(ns),
                         first, goto_functions, loopstoret(), loopstoret(),
                         ns, temp_context);

  return sum_checker.assertion_holds(goto_program, assertion, out,
                               max_memory_used, options, use_smt);
}

/*******************************************************************

 Function: assertion_holds_sum

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds. This is only
 a convenience wrapper.

\*******************************************************************/

bool assertion_holds_sum(
  const contextt &context,
  const value_setst &value_sets,
  goto_programt::const_targett &head,
  const goto_programt &goto_program,
  const goto_functionst &goto_functions,
  const assertion_infot& assertion,
  std::ostream &out,
  unsigned long &max_memory_used,
  const optionst& options,
  bool use_smt)
{
  contextt temp_context;
  namespacet ns(context, temp_context);
  summarizing_checkert sum_checker(value_sets, head, goto_functions,
          loopstoret(), loopstoret(), ns, temp_context);

  return sum_checker.assertion_holds(goto_program, assertion, out,
                               max_memory_used, options, use_smt);
}

/*******************************************************************

 Function: summarizing_checkert::assertion_holds

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds

\*******************************************************************/

bool summarizing_checkert::assertion_holds(
  const goto_programt &goto_program,
  const assertion_infot& assertion,
  std::ostream &out,
  unsigned long &max_memory_used,
  const optionst& options,
  bool use_smt)
{

  bool end = false;
  // Trivial case
  if(assertion.get_location()->guard.is_true())
  {
    out << std::endl << "ASSERTION IS TRIVIALLY TRUE" << std::endl;
    return true;
  }

  const bool slicing_option = !options.get_bool_option("no-slicing");
  const bool queries_option = options.get_bool_option("save-queries");
  const int verbose_option = options.get_int_option("verbose-solver");

  // Prepare the summarization context
  summarization_contextt summarization_context(goto_functions, value_sets,
		  imprecise_loops, precise_loops);
  summarization_context.analyze_functions(ns);

  // Load older summaries
  {
	const std::string& summary_file = options.get_option("load-summaries");
	if (!summary_file.empty()) {
	  summarization_context.deserialize_infos(summary_file);
	}
  }

  unsigned int count = 0;
  unsigned int start_interp = 1;
  unsigned int summaries_inlined = 0;
  while (!end && count < 2) // hardcoded (for a while) bound for inline - tries (but it's actually needed just 2 times for trivial case)
  {
	  // Prepare summary_info, start with the lazy variant, i.e.,
	  // all summaries are initialized as NONDET except those on the way
	  // to the target assertion, which are marked INLINE.
	  summary_infot summary_info;
	  summary_info.initialize(summarization_context, goto_program, assertion, summaries_inlined, 0, count == 0 ? 0 : 1);
	  // Prepare the decision and interpolation procedures
	  std::auto_ptr<prop_convt> decider;
	  std::auto_ptr<interpolating_solvert> interpolator;
	  {
		satcheck_opensmtt* opensmt = new satcheck_opensmtt(
				verbose_option,
				queries_option);
		bv_pointerst *deciderp = new bv_pointerst(ns, *opensmt);
		deciderp->unbounded_array = bv_pointerst::U_AUTO;
		decider.reset(deciderp);
		interpolator.reset(opensmt);
	  }

	  // TODO: In loop call symex_assertion_sum, with refining
	  // the summary_info based on the spurious counter-examples
	  // (or ad hoc at first)
	  partitioning_target_equationt equation(ns);
	  symex_assertion_sumt symex = symex_assertion_sumt(
			  summarization_context,
			  summary_info,
			  original_loop_head,
			  ns,
			  context,
			  *decider,
			  *interpolator,
			  equation
			  );

	  setup_unwind(symex, options);

	  end = symex.assertion_holds(goto_program, assertion,
			  std::cout /* FIXME: out */, max_memory_used, use_smt,
			  slicing_option);

	  if (end && interpolator->can_interpolate() /*if summaries are already substituted, then do not generate new ones*/)
	  {
		if (summaries_inlined == 0)
		{
			// Compute the reduction time
			double red_timeout = 0;
			const char* red_timeout_str = options.get_option("reduce-proof").c_str();
			if (strlen(red_timeout_str)) {
			char* result;
			red_timeout = strtod(red_timeout_str, &result);

			if (result == red_timeout_str) {
				std::cerr << "WARNING: Invalid value of reduction time fraction \"" <<
						red_timeout_str << "\". No reduction will be applied." << std::endl;
			} else {
				red_timeout = ((double)symex.get_solving_time()) / 1000 * red_timeout;
			}
		}
    
		// Extract the interpolation summaries here...
		interpolant_mapt itp_map;

		fine_timet before, after;
		before=current_time();
		equation.extract_interpolants(*interpolator, *decider, itp_map, red_timeout);
		after=current_time();
		std::cout /* FIXME: out */ << "INTERPOLATION TIME: "<< time2string(after-before) << std::endl;
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
			std::cout /* FIXME: out */ << "ASSERTIONS HOLD AFTER INLINING." << std::endl;
		} else {
			std::cout /* FIXME: out */ << "FUNCTION SUMMARIES (for " << summaries_inlined << " calls) WERE SUBSTITUTED SUCCESSFULLY." << std::endl;
		}
	  } else if (count == 0 && summaries_inlined != 0){
		  std::cout /* FIXME: out */ << "FUNCTION SUMMARIES (for " << summaries_inlined << " calls) AREN'T SUITABLE FOR CHECKING ASSERTION.\nTry to inline everything then.\n" << std::endl;
	  } else {
		  std::cout /* FIXME: out */ << "ASSERTIONS DON'T HOLD AFTER INLINING.\nA real bug found." << std::endl;
	  }
	  summaries_inlined = 0;
	  count++;
  }
  return end;
}

/*******************************************************************\

Function: summarizing_checkert::setup_unwind

  Inputs:

 Outputs:

 Purpose: Setup the unwind bounds.

\*******************************************************************/

void summarizing_checkert::setup_unwind(symex_assertion_sumt& symex, 
        const optionst& options)
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
