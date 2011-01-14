/*******************************************************************
 Module: Symbolic execution and deciding of a given goto-program

 Author: Aliaksei Tsitovich

 \*******************************************************************/

#ifndef SYMEX_ASSERTION_H_
#define SYMEX_ASSERTION_H_

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

#include "loopstore.h"

extern fine_timet global_satsolver_time;
extern fine_timet global_sat_conversion_time;

class symex_assertiont : public goto_symext
{
public:
  symex_assertiont(
    const value_setst &original_value_sets,
    goto_programt::const_targett &original_head,
    const namespacet &_ns,
    contextt &_context,
    symex_target_equationt &_target) : 
      goto_symext(_ns, _context, _target),
      equation(_target),
      value_sets(original_value_sets),
      original_loop_head(original_head) {};
  
  bool last_assertion_holds(
    const goto_programt &goto_program,
    std::ostream &out,
    unsigned long &max_memory_used,
    bool use_smt=false);
  
  bool assertion_holds(
    const goto_programt &goto_program,
    goto_programt::const_targett &assertion,
    std::ostream &out,
    unsigned long &max_memory_used,
    bool use_smt=false);
  
  bool equation_holds(
    symex_target_equationt &target,
    std::ostream &out,
    unsigned long &max_memory_used,
    bool use_smt=false);
  
  void to_equation(
    const contextt &context,
    contextt &temp_context,
    const value_setst &value_sets,
    goto_programt::const_targett &head,
    const goto_programt &goto_program,
    goto_programt::const_targett &assertion,
    symex_target_equationt &target,
    std::ostream &out,
    unsigned long &max_memory_used,
    bool use_smt);
  
  void slice_equation(
    const contextt &context,
    contextt &temp_context,
    symex_target_equationt &target,
    std::ostream &out) const;

protected:  
  symex_target_equationt &equation;
  const value_setst &value_sets;
  goto_programt::const_targett &original_loop_head;
  
  bool is_satisfiable(
    decision_proceduret &decision_procedure,
    std::ostream &out);
};

bool assertion_holds(
  const contextt &context,
  const value_setst &value_sets,
  goto_programt::const_targett &head,
  const goto_programt &goto_program,
  goto_programt::const_targett &assertion,  
  std::ostream &out,
  unsigned long &max_memory_used,  
  bool use_smt=false);

bool last_assertion_holds(
  const contextt &context,
  const value_setst &value_sets,
  goto_programt::const_targett &head,
  const goto_programt &goto_program,
  std::ostream &out,
  unsigned long &max_memory_used,
  bool use_smt=false);

bool assertion_holds(
  const contextt &context,
  const goto_programt &goto_program,
  goto_programt::const_targett &assertion,
  std::ostream &out,
  unsigned long &max_memory_used,
  bool use_smt=false);

#endif /*SYMEX_ASSERTION_H_*/
