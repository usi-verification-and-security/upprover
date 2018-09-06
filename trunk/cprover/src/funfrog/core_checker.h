/*******************************************************************

 Module: Assertion checker that extracts and uses function 
 summaries

 Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_SUMMARIZING_CHECKER_H
#define CPROVER_SUMMARIZING_CHECKER_H

#include <util/options.h>
#include <util/ui_message.h>
#include <goto-programs/goto_model.h>
#include <funfrog/solvers/solver_options.h>
#include "subst_scenario.h"

#include <memory>

class smt_assertion_no_partitiont;
class partitioning_target_equationt;
class prop_assertion_sumt;
class prepare_formulat;
class check_opensmt2t;
class symex_bmct;
class interpolating_solvert;
class prop_conv_solvert;
class symex_assertion_sumt;
class smtcheck_opensmt2t_cuf;
class smtcheck_opensmt2t_uf;
class smtcheck_opensmt2t_lra;
class smtcheck_opensmt2t_lia;
class satcheck_opensmt2t;


class core_checkert : private messaget
{
public:
  core_checkert(const goto_modelt & _goto_model, const optionst & _options,
                  ui_message_handlert & _message_handler, unsigned long & _max_memory_used);

  ~core_checkert() override;

  void initialize();
  bool assertion_holds(const assertion_infot& assertion, bool store_summaries_with_assertion);

#ifdef PRODUCE_PROOF
    //  bool check_sum_theoref_single(const assertion_infot& assertion);
    bool check_sum_theoref_single(const assertion_infot &assertion);
#endif // PRODUCE_PROOF

protected:
    const goto_modelt & goto_model;
    //symbol_tablet symex_symbol_table; MB: Symbol table needed only if we need information out of SYMEX about new symbols created there.
    // Currently, it seems we do not need this information
    const namespacet ns;
  const optionst &options;
  ui_message_handlert &message_handler;
  unsigned long &max_memory_used;
  check_opensmt2t* decider; // Can be Prop, LRA or UF solver!!
  subst_scenariot omega;
  init_modet init;
  std::unique_ptr<summary_storet> summary_store;
   solver_optionst solver_options; // Init once, use when ever create a new solver

  void initialize_solver();
  smtcheck_opensmt2t_uf * initialize__euf_solver();
  smtcheck_opensmt2t_cuf * initialize__cuf_solver();
  smtcheck_opensmt2t_lra * initialize__lra_solver();
  smtcheck_opensmt2t_lia * initialize__lia_solver();
  satcheck_opensmt2t * initialize__prop_solver();
  
  void initialize_solver_options();
  void initialize_solver_debug_options();
  void initialize__euf_option_solver();
  void initialize__cuf_option_solver();
  void initialize__lra_option_solver();
  void initialize__lia_option_solver();
  void initialize__prop_option_solver();
  
  void setup_unwind(symex_bmct& symex);
#ifdef PRODUCE_PROOF  
  void extract_interpolants(partitioning_target_equationt& equation);
#endif

  void report_success();
  void report_failure();
  void assertion_violated(prepare_formulat& prop,
		  std::map<irep_idt, std::string> &guard_expln);
  void assertion_violated (smt_assertion_no_partitiont& prop,
                  std::map<irep_idt, std::string> &guard_expln);

    const goto_functionst & get_goto_functions() const {
        return goto_model.goto_functions;
    }

    const goto_programt & get_main_function() const {
        return get_goto_functions().function_map.at(goto_functionst::entry_point()).body;
    }

    bool assertion_holds_(const assertion_infot & assertion, bool store_summaries_with_assertion);
    bool assertion_holds_smt_no_partition(const assertion_infot& assertion); // BMC alike version
    void slice_target(partitioning_target_equationt&);
    bool prepareSSA(symex_assertion_sumt& symex);
    bool refineSSA(symex_assertion_sumt & symex, const std::list<call_tree_nodet *> & functions_to_refine);

    bool is_option_set(std::string const & o) { return !options.get_option(o).empty();}

};

#endif
