/*******************************************************************

 Module: Assertion checker that extracts and uses function 
 summaries

 Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_SUMMARIZING_CHECKER_H
#define CPROVER_SUMMARIZING_CHECKER_H

#include <memory>
#include <util/options.h>
#include <util/ui_message.h>
#include "subst_scenario.h"

class smt_assertion_no_partitiont;
class prop_partitioning_target_equationt;
class smt_partitioning_target_equationt;
class prop_assertion_sumt;
class prepare_smt_formulat;
class check_opensmt2t;
class symex_bmct;
class interpolating_solvert;
class prop_conv_solvert;

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
    );

  ~summarizing_checkert() override;
  void initialize();
  void initialize_solver();
  void delete_and_initialize_solver(); // For replacing pop in the solver, remove once pop works
  bool last_assertion_holds();
  bool assertion_holds(const assertion_infot& assertion, bool store_summaries_with_assertion);
  bool assertion_holds_prop(const assertion_infot& assertion, bool store_summaries_with_assertion);
  bool assertion_holds_smt(const assertion_infot& assertion, bool store_summaries_with_assertion);
  bool assertion_holds_smt_no_partition(const assertion_infot& assertion); // BMC alike version
  void serialize(){
    omega.serialize(options.get_option("save-omega"));
  };

protected:

  const goto_programt &goto_program;
  const namespacet &ns;
  symbol_tablet &symbol_table;
  const optionst &options;
  ui_message_handlert &message_handler;
  unsigned long &max_memory_used;
  check_opensmt2t* decider; // Can be Prop, LRA or UF solver!!
  subst_scenariot omega;
  init_modet init;
  std::unique_ptr<summary_storet> summary_store;
  
  void setup_unwind(symex_bmct& symex);
#ifdef PRODUCE_PROOF  
  void extract_interpolants_smt (prepare_smt_formulat& prop, smt_partitioning_target_equationt& equation);
  void extract_interpolants_prop (prop_assertion_sumt& prop, prop_partitioning_target_equationt& equation,
            prop_conv_solvert& decider_prop, interpolating_solvert& interpolator);
#endif
  void report_success();
  void report_failure();
  void assertion_violated(prepare_smt_formulat& prop,
		  std::map<irep_idt, std::string> &guard_expln);
  void assertion_violated (smt_assertion_no_partitiont& prop,
                  std::map<irep_idt, std::string> &guard_expln);

    const goto_functionst & get_goto_functions() const {
        return omega.get_goto_functions();
    }

};

init_modet get_init_mode(const std::string& str);
refinement_modet get_refine_mode(const std::string& str);


#endif
