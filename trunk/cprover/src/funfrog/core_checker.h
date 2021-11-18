/*******************************************************************

 Module: Assertion checker that extracts and uses function 
 summaries
\*******************************************************************/

#ifndef CPROVER_SUMMARIZING_CHECKER_H
#define CPROVER_SUMMARIZING_CHECKER_H

#include <util/options.h>
#include <util/ui_message.h>
#include <goto-programs/goto_model.h>
#include <funfrog/solvers/solver_options.h>
#include "solvers/smtcheck_opensmt2_lra.h"
#include "solvers/smtcheck_opensmt2_uf.h"
#include "subst_scenario.h"
#include <memory>

class prepare_formula_no_partitiont;
class partitioning_target_equationt;
class formula_managert;
class check_opensmt2t;
class symex_bmct;
class interpolating_solvert;
class solvert;
class prop_conv_solvert;
class symex_assertion_sumt;
class smtcheck_opensmt2t_cuf;
class smtcheck_opensmt2t_lia;
class satcheck_opensmt2t;
class ssa_solvert;

class core_checkert : public messaget
{
public:
  core_checkert(const goto_modelt & _goto_model, optionst & _options,
                ui_message_handlert & _message_handler, unsigned long & _max_memory_used);

  ~core_checkert() override;

  void initialize_call_info();
  bool assertion_holds(const assertion_infot& assertion, bool store_summaries_with_assertion);

#ifdef PRODUCE_PROOF
    //  bool check_sum_theoref_single(const assertion_infot& assertion);
    bool check_sum_theoref_single(const assertion_infot &assertion);
    // public method that allows upgrade check to write the subst scenario into a __omega file
    void serialize(){
        omega.serialize(options.get_option("save-omega"));
    }
    // public method that allows upgrade check to read the subst scenario from __omega file
    void deserialize(const goto_programt & goto_program){
        omega.deserialize(options.get_option("save-omega"), goto_program);
    }
#endif // PRODUCE_PROOF
    
protected:
    const goto_modelt & goto_model;
    //symbol_tablet symex_symbol_table; MB: Symbol table needed only if we need information out of SYMEX about new symbols created there.
    // Currently, it seems we do not need this information
    const namespacet ns;
  optionst &options;
  ui_message_handlert &message_handler;
  unsigned long &max_memory_used;
  std::shared_ptr<ssa_solvert> decider;  //summary_validation required the ownership
  std::shared_ptr<summary_storet> summary_store; //summary_validation required the ownership
  subst_scenariot omega;
  init_modet init;
  solver_optionst solver_options; // Init once, use when ever create a new solver
  
  void initialize_solver();
  void initialize_summary_store();
  void init_solver_and_summary_store();
  std::unique_ptr<ssa_solvert> initialize__euf_solver();
  std::unique_ptr<ssa_solvert> initialize__cuf_solver();
  std::unique_ptr<ssa_solvert> initialize__lra_solver();
  std::unique_ptr<ssa_solvert> initialize__lia_solver();
  std::unique_ptr<ssa_solvert> initialize__prop_solver();
  
  void initialize_solver_options();
  void initialize_solver_debug_options();
  void initialize__euf_option_solver();
  void initialize__cuf_option_solver();
  void initialize__lra_option_solver();
  void initialize__lia_option_solver();
  void initialize__prop_option_solver();
  
  //void setup_unwind(symex_bmct& symex);  //no usage anymore
#ifdef PRODUCE_PROOF  
  void extract_interpolants(partitioning_target_equationt& equation);
#endif
  
  void report_success();
  void report_failure();
  void assertion_violated(formula_managert& prop,
                          std::map<irep_idt, std::string> &guard_expln);
  void assertion_violated_no_partition(prepare_formula_no_partitiont &prop,
                                       std::map<irep_idt, std::string> &guard_expln);

    const goto_functionst & get_goto_functions() const {
        return goto_model.goto_functions;
    }

    const goto_programt & get_main_function() const {
        //the entry point is __CPROVER_start
        return get_goto_functions().function_map.at(goto_functionst::entry_point()).body;
    }	
    
    bool assertion_holds_smt(const assertion_infot &assertion, bool store_summaries_with_assertion);
    bool assertion_holds_smt_no_partition(const assertion_infot& assertion); // BMC alike version
    bool assertion_holds_smt_wt_lattice(const assertion_infot& assertion,
          bool store_summaries_with_assertion); // Lattice refinement version
    void slice_target(partitioning_target_equationt&);
    bool prepareSSA(symex_assertion_sumt& symex);
    bool refineSSA(symex_assertion_sumt & symex, const std::list<call_tree_nodet *> & functions_to_refine);

    bool is_option_set(std::string const & o) { return !options.get_option(o).empty();}
    
    void delete_and_initialize_solver();
    
};

#endif
