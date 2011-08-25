/*******************************************************************\

 Module: String Loop Summarization

 Author: CM Wintersteiger
         Aliaksei Tsitovich

\*******************************************************************/

#include <fstream>
#include <sstream>
#include <algorithm>

#include <ansi-c/c_types.h>
#include <ansi-c/expr2c.h>
#include <mp_arith.h>
#include <expr_util.h>
#include <std_expr.h>
#include <i2string.h>
#include <config.h>
#include <langapi/language_util.h>

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>
#include <goto-programs/string_abstraction.h>
#include <goto-symex/goto_symex.h>
#include <goto-symex/symex_target_equation.h>

#include "string_summarization.h"
#include "string_utils.h"
#include "pointer_expr.h"

// Invariants that we use
#include "invariants/zero_termination.h"
#include "invariants/iterator_bounds.h"
#include "invariants/iterator_bounds2.h"
#include "invariants/strong_bounds.h"
#include "invariants/string_length.h"
#include "invariants/decreasing_length.h"
#include "invariants/null_pointer.h"
#include "invariants/pointer_offset.h"
#include "invariants/pointer_object.h"
#include "invariants/constant_tracker.h"
#include "invariants/equalities.h"
#include "invariants/inequalities.h"
#include "invariants/disequalities.h"
#include "invariants/ti_less_greater_all.h"
#include "invariants/ti_less_greater_numeric.h"
#include "invariants/ti_or_less_greater_all.h"
#include "invariants/ti_or_less_greater_all.h"
#include "invariants/ti_max_less_greater.h"
#include "invariants/ti_sum_less_greater.h"
#include "invariants/sti_gzero_implies_less_greater_all.h"
#include "invariants/sti_gzero_implies_or_less_greater_all.h"


/*******************************************************************\

 Function: string_summarizationt::string_summarizationt

 Inputs:

 Outputs:

 Purpose: Constructor. Only needs to schedule tests.

\*******************************************************************/

string_summarizationt::string_summarizationt(
  contextt &context,
  goto_functionst &_goto_functions,
  const loopstoret &_imprecise_loops,
  const loopstoret &_precise_loops,
  value_setst &_value_sets,
  const std::string &_stats_dir,
  const optionst &_opts) :
    summarizationt(context, _goto_functions,
                   _imprecise_loops, _precise_loops,
                   _value_sets, _stats_dir, _opts)
{
  if(options.get_bool_option("zt"))
    schedule(new zero_termination_invariant_testt(context));

  if(options.get_bool_option("ib"))
    schedule(new iterator_bounds_invariant_testt(context));

  if(options.get_bool_option("i2"))
    schedule(new iterator_bounds2_invariant_testt(context));

  if(options.get_bool_option("sb"))
    schedule(new strong_bounds_invariant_testt(context));

  if(options.get_bool_option("sl"))
    schedule(new string_length_invariant_testt(context));

  if(options.get_bool_option("dl"))
    schedule(new decreasing_length_invariant_testt(context));

  if(options.get_bool_option("np"))
    schedule(new null_pointer_invariant_testt(context));

  if(options.get_bool_option("ct"))
    schedule(new constant_tracker_invariant_testt(context));

  if(options.get_bool_option("poff"))
    schedule(new pointer_offset_invariant_testt(context));

  if(options.get_bool_option("pobj"))
    schedule(new pointer_object_invariant_testt(context));

  if(options.get_bool_option("eq"))
    schedule(new equalities_invariant_testt(context));

  if(options.get_bool_option("neq"))
    schedule(new inequalities_invariant_testt(context));

  if(options.get_bool_option("ineq"))
    schedule(new disequalities_invariant_testt(context));

  if(options.get_bool_option("ti1"))
    schedule(new ti_less_greater_numeric_invariant_testt(context));

  if(options.get_bool_option("ti2"))
    schedule(new ti_less_greater_all_invariant_testt(context));

  if(options.get_bool_option("ti3"))
    schedule(new ti_sum_less_greater_invariant_testt(context));
    
  if(options.get_bool_option("ti4"))
    schedule(new ti_max_less_greater_invariant_testt(context));
    
  if(options.get_bool_option("ti5"))
    schedule(new ti_or_less_greater_all_invariant_testt(context));

  if(options.get_bool_option("st1"))
    schedule(new sti_gzero_implies_less_greater_all_invariant_testt(context));

  if(options.get_bool_option("st2"))
    schedule(new sti_gzero_implies_or_less_greater_all_invariant_testt(context));

}
