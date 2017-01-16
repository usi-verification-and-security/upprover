#ifndef CPROVER_THEORY_REFINER_H
#define CPROVER_THEORY_REFINER_H

#include <memory>
#include <options.h>
#include <ui_message.h>
#include <solvers/flattening/bv_pointers.h>
#include "symex_assertion_sum.h"
#include "assertion_sum.h"
#include "prop_assertion_sum.h"
#include "smt_assertion_sum.h"
#include "refiner_assertion_sum.h"
#include "prop_partitioning_target_equation.h"
#include "smt_partitioning_target_equation.h"

class theory_refinert:public messaget
{
public:
  theory_refinert(
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
                options.get_unsigned_int_option("unwind")),

      message_handler (_message_handler),
      max_memory_used(_max_memory_used),
      omega(summarization_context, goto_program)
  {
    set_message_handler(_message_handler);
  };

  void initialize();
  bool assertion_holds_smt(const assertion_infot& assertion, bool store_summaries_with_assertion);

  const goto_programt &goto_program;
  const namespacet &ns;
  symbol_tablet &symbol_table;
  const optionst &options;
  summarization_contextt summarization_context;
  ui_message_handlert &message_handler;
  unsigned long &max_memory_used;
  check_opensmt2t* decider; // currently UF solver
  subst_scenariot omega;
  
  void setup_unwind(symex_assertion_sumt& symex);
  void report_success();
  void report_failure();
};

#endif
