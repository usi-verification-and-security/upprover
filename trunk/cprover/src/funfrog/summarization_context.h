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

typedef enum {
  FORCE_INLINING,
  RANDOM_SUBSTITUTION,
  SLICING_RESULT
  // anything else?
}
  refinement_modet;

typedef enum {
  ALL_SUBSTITUTING,
  ALL_HAVOCING
  // anything else?
}
  init_modet;

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
  
  const goto_functionst& get_functions() const { return functions; }
  
  const goto_functionst::goto_functiont& get_function(
    const irep_idt& function_id) const 
  {
    return functions.function_map.find(function_id)->second;
  }
  
  const function_infot& get_function_info(const irep_idt& function_id) const {
    return function_infos.find(function_id)->second;
  }
  
  function_infot& get_function_info(const irep_idt& function_id) {
    return function_infos.find(function_id)->second;
  }

  void analyze_functions(const namespacet& ns) {
    function_infos.find(functions.main_id())->second.analyze_globals(*this, ns);
  }
  
  void deserialize_infos(const std::string& file) {
    function_infot::deserialize_infos(file, function_infos);
  }
  
  void serialize_infos(const std::string& file) {
    function_infot::serialize_infos(file, function_infos);
  }

private:
  const goto_functionst &functions;
  const value_setst &value_sets;
  const loopstoret &imprecise_loops;
  const loopstoret &precise_loops;
  function_infost function_infos;
};

#endif
