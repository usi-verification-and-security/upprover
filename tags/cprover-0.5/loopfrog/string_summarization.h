/*******************************************************************\

Module: String Loop Summarization

Author: CM Wintersteiger
        Aliaksei Tsitovich

\*******************************************************************/

#ifndef _LOOPFROG_STRING_SUMMARIZATION_H_
#define _LOOPFROG_STRING_SUMMARIZATION_H_

/* this is a string-related summarization "plugin" */

#include <simplify_expr.h>

#include "invariants/invariant_test.h"

#include "summarization.h"
#include "summary.h"
#include "symex_assertion.h"
#include "value_set_duplication_adaptor.h"

class string_summarizationt : public summarizationt
{
public:
  string_summarizationt(
    contextt &context, 
    goto_functionst &_goto_functions,
    const loopstoret &_imprecise_loops,
    const loopstoret &_precise_loops,
    value_setst &_value_sets,
    const std::string &_stats_dir,
    const optionst &_opts);
  
  virtual ~string_summarizationt( void ) {};  
};

#endif 
