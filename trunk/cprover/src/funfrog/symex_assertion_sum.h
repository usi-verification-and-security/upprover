/*******************************************************************
 Module: Symbolic execution and deciding of a given goto-program
 using and generating function summaries. Based on symex_asserion.h.

 Author: Ondrej Sery

 \*******************************************************************/

#ifndef SYMEX_ASSERTION_SUM_H_
#define SYMEX_ASSERTION_SUM_H_

#include <stack>

#include <solvers/flattening/sat_minimizer.h>
#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>
#include <goto-symex/goto_symex.h>
#include <goto-symex/symex_target_equation.h>
#include <namespace.h>

#include <base_type.h>
#include <time_stopping.h>
#include <fstream>
#include <goto-symex/slice.h>

#include <loopfrog/loopstore.h>

#include "assertion_info.h"
#include "summary_info.h"
#include "summarization_context.h"

extern fine_timet global_satsolver_time;
extern fine_timet global_sat_conversion_time;

class symex_assertion_sumt : public goto_symext
{
public:
  symex_assertion_sumt(
          const summarization_contextt &_summarization_context,
          const summary_infot &_summary_info,
          goto_programt::const_targett &original_head,
          const namespacet &_ns,
          contextt &_context,
          symex_target_equationt &_target
          ) :
          goto_symext(_ns, _context, _target),
          summarization_context(_summarization_context),
          summary_info(_summary_info),
          equation(_target),
          original_loop_head(original_head) {};

  bool assertion_holds(
    const goto_programt &goto_program,
    const assertion_infot &assertion,
    std::ostream &out,
    unsigned long &max_memory_used,
    bool use_smt=false);
  
  virtual void symex_step(
    const goto_functionst &goto_functions,
    statet &state);

  void slice_equation(
    const contextt &context,
    contextt &temp_context,
    symex_target_equationt &target,
    std::ostream &out) const;

protected:
  // Shared information about the program and sumamries to be used during
  // analysis
  const summarization_contextt &summarization_context;

  // Which functions should be summarized, abstracted from, and which inlined.
  const summary_infot &summary_info;
  
  symex_target_equationt &equation;
  goto_programt::const_targett &original_loop_head;

  bool is_satisfiable(
    decision_proceduret &decision_procedure,
    std::ostream &out);
};

#endif /*SYMEX_ASSERTION_SUM_H_*/
