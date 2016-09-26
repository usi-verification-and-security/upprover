/*******************************************************************

 Module: Assertion checker that extracts and uses function 
 summaries

 Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_SUMMARIZING_CHECKER_H
#define CPROVER_SUMMARIZING_CHECKER_H

#include <memory>
#include <options.h>
#include <ui_message.h>
#include <solvers/flattening/bv_pointers.h>
#include "symex_assertion_sum.h"
#include "prop_assertion_sum.h"
#include "refiner_assertion_sum.h"

#include "solvers/smtcheck_opensmt2_lra.h"

class summarizing_checkert:public messaget
{
public:
  summarizing_checkert(
    const goto_programt &_goto_program,
    const goto_functionst &_goto_functions,
    const namespacet &_ns,
    symbol_tablet &_symbol_table,
    const optionst& _options,
    ui_message_handlert &_message_handler,

    unsigned long &_max_memory_used
    ) :
      goto_program(_goto_program),
      ns(_ns),
      symbol_table(_symbol_table),
      options(_options),
      summarization_context(
                _goto_functions,
                options.get_int_option("unwind")),

      message_handler (_message_handler),
      max_memory_used(_max_memory_used),
      omega(summarization_context, goto_program)
  {set_message_handler(_message_handler);};

  void initialize();
  bool last_assertion_holds();
  bool assertion_holds(const assertion_infot& assertion, bool store_summaries_with_assertion);
  void serialize(){
    omega.serialize(options.get_option("save-omega"));
  };

protected:

  const goto_programt &goto_program;
  const namespacet &ns;
  symbol_tablet &symbol_table;
  const optionst &options;
  summarization_contextt summarization_context;
  ui_message_handlert &message_handler;
  unsigned long &max_memory_used;
//  std::auto_ptr<prop_convt> decider;
//  std::auto_ptr<interpolating_solvert> interpolator;

  smtcheck_opensmt2t* decider;

  subst_scenariot omega;
  init_modet init;
  
  void setup_unwind(symex_assertion_sumt& symex);
  void extract_interpolants (prop_assertion_sumt& prop, partitioning_target_equationt& equation);
  void report_success();
  void report_failure();
  void assertion_violated(prop_assertion_sumt& prop);
};

init_modet get_init_mode(const std::string& str);
refinement_modet get_refine_mode(const std::string& str);
coloring_modet get_coloring_mode(const std::string& str);

#endif
