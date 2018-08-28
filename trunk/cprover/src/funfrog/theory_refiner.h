#ifndef CPROVER_THEORY_REFINER_H
#define CPROVER_THEORY_REFINER_H

#include <memory>
#include <util/options.h>
#include <util/ui_message.h>
#include "subst_scenario.h"
#include <funfrog/solvers/solver_options.h>

class smtcheck_opensmt2t_cuf;
class symex_assertion_sumt;
class partitioning_target_equationt;

class theory_refinert:public messaget
{
public:
  theory_refinert(
    const goto_programt &_goto_program,
    const goto_functionst &_goto_functions,
    const symbol_tablet &_symbol_table,
    const optionst& _options,
    ui_message_handlert &_message_handler
    ) :
      goto_program(_goto_program),
      symbol_table(_symbol_table),
      options(_options),
      message_handler (_message_handler),
      omega(_goto_functions, options.get_unsigned_int_option("unwind"))
  {
    set_message_handler(_message_handler);
  };

  // KE: can we delete the object once deleting the refiner?
  virtual ~theory_refinert();
  
  void initialize();
  bool assertion_holds_smt(const assertion_infot& assertion, bool store_summaries_with_assertion);
    void slice_target(partitioning_target_equationt & equation);
  
private:
  const goto_programt &goto_program;
  const symbol_tablet &symbol_table;
  const optionst &options;
  ui_message_handlert &message_handler;
  smtcheck_opensmt2t_cuf* decider; // CUF solver
  subst_scenariot omega;
  solver_optionst solver_options;
  
  //void setup_unwind(symex_assertion_sumt& symex);
  void report_success();
  void report_failure();
};

#endif
