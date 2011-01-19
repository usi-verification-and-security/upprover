/*******************************************************************

 Module: Keeps the information shared by a single summarization
 task.

 Author: Ondrej Sery

\*******************************************************************/

#ifndef SUMMARIZATION_CONTEXT_H_
#define SUMMARIZATION_CONTEXT_H_

#include <pointer-analysis/value_set_analysis.h>
#include <goto-programs/goto_functions.h>

#include "function_info.h"

// Information shared by a single summarization task.
class summarization_contextt {
public:
  summarization_contextt(
          const goto_functionst &_functions,
          const value_setst &_value_sets,
          const loopstoret &_imprecise_loops,
          const loopstoret &_precise_loops
          ) : 
          functions(_functions),
          value_sets(_value_sets),
          imprecise_loops(_imprecise_loops),
          precise_loops(_precise_loops) {}

  const goto_functionst &functions;
  const value_setst &value_sets;
  const loopstoret &imprecise_loops;
  const loopstoret &precise_loops;
  function_infost function_infos;
};

#endif /*SUMMARIZATION_CONTEXT_H_*/
