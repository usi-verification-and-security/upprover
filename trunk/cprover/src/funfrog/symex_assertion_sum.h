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

#include "../loopfrog/loopstore.h"

extern fine_timet global_satsolver_time;
extern fine_timet global_sat_conversion_time;

class symex_assertion_sumt : public goto_symext
{
public:
  symex_assertion_sumt(
    const value_setst &original_value_sets,
    goto_programt::const_targett &original_head,
    const loopstoret &_imprecise_loops,
    const loopstoret &_precise_loops,
    const namespacet &_ns,
    contextt &_context,
    symex_target_equationt &_target) :
      goto_symext(_ns, _context, _target),
      imprecise_loops(_imprecise_loops),
      precise_loops(_precise_loops),
      equation(_target),
      value_sets(original_value_sets),
      original_loop_head(original_head) {};

  bool assertion_holds(
    const goto_programt &goto_program,
    goto_programt::const_targett &assertion,
    std::ostream &out,
    unsigned long &max_memory_used,
    bool use_smt=false);

  void slice_equation(
    const contextt &context,
    contextt &temp_context,
    symex_target_equationt &target,
    std::ostream &out) const;

protected:
  // Summaries to apply in the analysis
  const loopstoret &imprecise_loops;
  const loopstoret &precise_loops;

  // Function summaries to use/fill
  // TODO
  
  // Info about which calls to substitute by summaries and
  // which to inline
  // TODO
  
  symex_target_equationt &equation;
  const value_setst &value_sets;
  goto_programt::const_targett &original_loop_head;

  bool is_satisfiable(
    decision_proceduret &decision_procedure,
    std::ostream &out);
};

#endif /*SYMEX_ASSERTION_SUM_H_*/
