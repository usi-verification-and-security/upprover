/*******************************************************************

 Module: Assertion checker that extracts and uses function 
 summaries

 Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_SUMMARIZING_CHECKER_H
#define CPROVER_SUMMARIZING_CHECKER_H

#include <memory>
#include <options.h>

#include "symex_assertion_sum.h"
#include "prop_assertion_sum.h"
#include "refiner_assertion_sum.h"
#include "solvers/satcheck_opensmt.h"

class summarizing_checkert
{
public:
  summarizing_checkert(
    const goto_programt &_goto_program,
    const value_setst &_value_sets,
    const goto_functionst &_goto_functions,
    const loopstoret &_imprecise_loops,
    const loopstoret &_precise_loops,
    const namespacet &_ns,
    contextt &_context,
    const optionst& _options,
    std::ostream &_out,
    unsigned long &_max_memory_used
    ) :
      goto_program(_goto_program),
      ns(_ns),
      context(_context),
      options(_options),
      summarization_context(
                _goto_functions,
                _value_sets,
                _imprecise_loops,
                _precise_loops),
      out(_out),
      max_memory_used(_max_memory_used),
      equation(_ns),
      summary_info(NULL)
  {};

  void initialize();
  bool last_assertion_holds();
  bool assertion_holds(const assertion_infot& assertion);

protected:

  const goto_programt &goto_program;
  const namespacet &ns;
  contextt &context;
  const optionst &options;
  summarization_contextt summarization_context;
  std::ostream &out;
  unsigned long &max_memory_used;
  std::auto_ptr<prop_convt> decider;
  std::auto_ptr<interpolating_solvert> interpolator;
  partitioning_target_equationt equation;
  satcheck_opensmtt* opensmt;
  summary_infot summary_info;
  init_modet init;
  
  void setup_unwind(symex_assertion_sumt& symex);
  double compute_reduction_timeout(double solving_time);
  void extract_interpolants (partitioning_target_equationt& equation, double red_timeout);
};

init_modet get_init_mode(const std::string& str);
refinement_modet get_refine_mode(const std::string& str);

#endif
