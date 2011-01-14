/*******************************************************************

 Module: Assertion checker that extracts and uses function 
 summaries

 Author: Ondrej Sery

\*******************************************************************/

#ifndef SUMMARIZING_CHECKER_H_
#define SUMMARIZING_CHECKER_H_

#include <pointer-analysis/value_set_analysis.h>

#include <loopfrog/loopstore.h>
#include <loopfrog/call_stack.h>

#include "assertion_info.h"

class summarizing_checkert
{
public:
  summarizing_checkert(
    const value_setst &original_value_sets,
    goto_programt::const_targett &original_head,
    const loopstoret &_imprecise_loops,
    const loopstoret &_precise_loops,
    const namespacet &_ns,
    contextt &_context) :
//      goto_symext(_ns, _context, _target),
      imprecise_loops(_imprecise_loops),
      precise_loops(_precise_loops),
      value_sets(original_value_sets),
      original_loop_head(original_head) {};

  bool last_assertion_holds(
    const goto_programt &goto_program,
    std::ostream &out,
    unsigned long &max_memory_used,
    bool use_smt=false);

  bool assertion_holds(
    const goto_programt &goto_program,
    const assertion_infot& assertion,
    std::ostream &out,
    unsigned long &max_memory_used,
    bool use_smt=false);

protected:
  // Summaries to apply in the analysis
  const loopstoret &imprecise_loops;
  const loopstoret &precise_loops;
  
  const value_setst &value_sets;
  goto_programt::const_targett &original_loop_head;
};

bool assertion_holds_sum(
  const contextt &context,
  const value_setst &value_sets,
  goto_programt::const_targett &head,
  const goto_programt &goto_program,
  const assertion_infot& assertion,
  std::ostream &out,
  unsigned long &max_memory_used,
  bool use_smt=false);

bool last_assertion_holds_sum(
  const contextt &context,
  const value_setst &value_sets,
  goto_programt::const_targett &head,
  const goto_programt &goto_program,
  std::ostream &out,
  unsigned long &max_memory_used,
  bool use_smt=false);

bool assertion_holds_sum(
  const contextt &context,
  const goto_programt &goto_program,
  const assertion_infot& assertion,
  std::ostream &out,
  unsigned long &max_memory_used,
  bool use_smt=false);

#endif /*SUMMARIZING_CHECKER_H_*/

