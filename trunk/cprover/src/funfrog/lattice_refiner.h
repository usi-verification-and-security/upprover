/* 
 * File:   lattice_refinert.h
 * Author: karinek
 *
 * Created on 18 July 2017, 14:21
 */

#ifndef LATTICE_REFINERT_H
#define LATTICE_REFINERT_H

#include "lattice_refiner_expr.h"
#include <options.h>
#include <symbol_table.h>
#include "solvers/smtcheck_opensmt2.h"
#include "smt_partitioning_target_equation.h"
#include "symex_assertion_sum.h"

class lattice_refinert:public messaget {
public:
    lattice_refinert(
        const optionst& _options,
        ui_message_handlert &_message_handler, 
        summarization_contextt &_summarization_context)
        : options(_options),
          summarization_context(_summarization_context),
          is_lattice_ref_on(options.get_option("load-sum-model").size()>0),
          refineTryNum(0),
          flag_can_refine(true),
          final_result_of_refinement(lattice_refinert::resultt::UNKNOWN),
          is_did_pop(false)
    {
        no_error_trace = options.get_bool_option("no-error-trace"); // KE: can be changed to some other indicator    
        set_message_handler(_message_handler);
        initialize();
    }
    
    virtual ~lattice_refinert() {
        // delete the model!
    }
    
  void initialize();
  
  void refine(smtcheck_opensmt2t &decider, symex_assertion_sumt& symex, bool is_solver_ret_SAT);
  
  bool refine_SSA(smtcheck_opensmt2t &decider, symex_assertion_sumt& symex);
  
  unsigned get_models_count() const { return models.size(); }
  
  unsigned get_refined_functions_size();
  
  unsigned get_summaries_from_lattice_count(bool is_first_iteration);
  
  unsigned get_summaries_refined_via_lattice_count();
  
  // We check once, before delete of decider, and keep it for later
  bool can_refine() { 
    if (!is_lattice_ref_on) return false; 
  
    return flag_can_refine; 
  } 
 
  bool is_end() { 
    return ((!can_refine()) 
          || (can_refine() && final_result_of_refinement != lattice_refinert::resultt::UNKNOWN)); 
  }
  
  bool is_required_init_solver() { return is_did_pop;} // Only if we did pop we must to reset the solver
  
protected:
  enum class resultt { UNKNOWN=0, SAT, UNSAT };
  
  resultt final_result_of_refinement;
  
private:
  const optionst &options; 
  bool is_lattice_ref_on;
  bool flag_can_refine;
  unsigned refineTryNum;
  bool no_error_trace;
  bool is_did_pop;
  
  // Shared information about summaries to be used during analysis
  summarization_contextt &summarization_context;

  /* Function declaration, head of the model - it is a map to support many models */
  std::map<std::string, lattice_refiner_modelt *> models; // Declare of func + its model
  std::map<std::string, SymRef> declare2literal; // Needed only for refine what openSMT can't express
  std::set<lattice_refiner_exprt *> expr2refine; // Keep per expression, next options to refine
  // Top is what we use currently to refine the expression
  
  void load_models(std::string list_of_models_fs); // Load all the models
  
  // Check the result
  bool process_SAT_result();
  bool process_UNSAT_result();
  bool process_solver_result(bool is_solver_ret_SAT); // KE: will call to SAT/UNSAT process result per expression
  
  bool can_refine(const smtcheck_opensmt2t &decider, const symex_assertion_sumt& symex) const;
  SymRef get_entry_point(smtcheck_opensmt2t &decider,
                        const std::string key_entry_orig,
                        const std::string key_entry, 
                        const exprt &expr, 
                        const exprt::operandst &operands);
  std::string gen_entry_point_name(smtcheck_opensmt2t &decider, 
                                    const std::string key_entry_orig, 
                                    const exprt &expr, 
                                    const exprt::operandst &operands);
  void add_expr_to_refine(smtcheck_opensmt2t &decider, symex_assertion_sumt& symex);
  void set_front_heuristic() { /* TODO */ } // Will change the front/order of expr2refine
  
  void pop_summaries(std::set<irep_idt>* to_pop, lattice_refiner_exprt *node);
  
  smt_summaryt& get_summary(const irep_idt& function_id);
  const summary_idst& get_summary_ids(const irep_idt& function_id);
  const exprt::operandst &fabricate_parameters(
        const irep_idt& function_id, 
        smtcheck_opensmt2t &decider,  
        symex_assertion_sumt& symex,
        const source_locationt& source_location,
        const exprt::operandst &call_info_operands);
  
  void instantiate_fact(const irep_idt& function_id, lattice_refiner_exprt *expr, 
          smtcheck_opensmt2t &decider, symex_assertion_sumt& symex, const exprt& lhs);
};

#endif /* LATTICE_REFINERT_H */