/*******************************************************************

 Module: Keeps the information shared by a single summarization
 task.

 Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_SUMMARIZATION_CONTEXT_H
#define CPROVER_SUMMARIZATION_CONTEXT_H

#include <pointer-analysis/value_set_analysis.h>
#include <goto-programs/goto_functions.h>
#include <loopfrog/loopstore.h>

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
          precise_loops(_precise_loops) 
  {
    for (goto_functionst::function_mapt::const_iterator it =
            functions.function_map.begin();
            it != functions.function_map.end();
            ++it) {
      function_infos.insert(function_infost::value_type(
        it->first, function_infot(it->first)));
    }
  }

  const interpolantst& get_summaries(irep_idt function_id) const {
    return function_infos.find(function_id)->second.get_summaries();
  }

  void analyze_functions(const namespacet& ns) {
    function_infos.find(functions.main_id())->second.analyze_globals(*this, ns);
  }

  const goto_functionst &functions;
  const value_setst &value_sets;
  const loopstoret &imprecise_loops;
  const loopstoret &precise_loops;
  function_infost function_infos;
};

#endif
