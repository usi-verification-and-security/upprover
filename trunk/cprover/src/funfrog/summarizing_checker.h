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
#include "summarization_context.h"
#include "summarization_context_fwd.h"
#include "subst_scenario.h"
#include "utils/coloring_mode.h"

class smt_assertion_no_partitiont;
class prop_partitioning_target_equationt;
class smt_partitioning_target_equationt;
class prop_assertion_sumt;
class smt_assertion_sumt;
class check_opensmt2t;
class symex_bmct;
class interpolating_solvert;

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
                options.get_unsigned_int_option("unwind")),

      message_handler (_message_handler),
      max_memory_used(_max_memory_used),
      omega(summarization_context, goto_program)
  {
    set_message_handler(_message_handler);
  };

  void initialize();
  void initialize_solver();
  void delete_and_initialize_solver(); // For replacing pop in the solver, remove once pop works
  bool last_assertion_holds();
  bool assertion_holds(const assertion_infot& assertion, bool store_summaries_with_assertion);
  bool assertion_holds_prop(const assertion_infot& assertion, bool store_summaries_with_assertion);
  bool assertion_holds_smt(const assertion_infot& assertion, bool store_summaries_with_assertion);
  bool assertion_holds_smt_no_partition(const assertion_infot& assertion, 
          bool store_summaries_with_assertion); // BMC alike version
  void serialize(){
    omega.serialize(options.get_option("save-omega"));
  };

    // MB: not used at the moment, as of 13.2.2018
    //void list_templates(smt_assertion_sumt &prop, smt_partitioning_target_equationt &equation);
protected:

  const goto_programt &goto_program;
  const namespacet &ns;
  symbol_tablet &symbol_table;
  const optionst &options;
  summarization_contextt summarization_context;
  ui_message_handlert &message_handler;
  unsigned long &max_memory_used;
  check_opensmt2t* decider; // Can be Prop, LRA or UF solver!!
  subst_scenariot omega;
  init_modet init;
  
  void setup_unwind(symex_bmct& symex);
#ifdef PRODUCE_PROOF  
  void extract_interpolants_smt (smt_assertion_sumt& prop, smt_partitioning_target_equationt& equation);
  void extract_interpolants_prop (prop_assertion_sumt& prop, prop_partitioning_target_equationt& equation,
            std::unique_ptr<prop_conv_solvert>& decider_prop, std::unique_ptr<interpolating_solvert>& interpolator);
#endif
  void report_success();
  void report_failure();
  void assertion_violated(smt_assertion_sumt& prop,
		  std::map<irep_idt, std::string> &guard_expln);
  void assertion_violated (smt_assertion_no_partitiont& prop,
                  std::map<irep_idt, std::string> &guard_expln);
};

init_modet get_init_mode(const std::string& str);
refinement_modet get_refine_mode(const std::string& str);
coloring_modet get_coloring_mode(const std::string& str);

#endif
