/* 
 * File:   lattice_refinert.h
 * Author: karinek
 *
 * Created on 18 July 2017, 14:21
 */

#ifndef LATTICE_REFINERT_H
#define LATTICE_REFINERT_H

#include "lattice_refiner_model.h"
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
        smtcheck_opensmt2t &_decider)
        : options(_options),
          is_lattice_ref_on(options.get_option("load-sum-model").size()>0),
          decider(_decider),
          refineTryNum(0)
    {
        set_message_handler(_message_handler);
        initialize();
    }
    
    virtual ~lattice_refinert() {
        // delete the model!
    }
    
  void initialize();
  
  void refine(smt_partitioning_target_equationt &equation,
              symex_assertion_sumt& symex);
  
  bool refine_SSA(const smtcheck_opensmt2t &decider, symex_assertion_sumt& symex);
  
  unsigned int summaries_count2refine(const smtcheck_opensmt2t& decider, const symex_assertion_sumt& symex) const;

  unsigned int get_models_count() const { return models.size(); }
  
  unsigned int get_refined_functions_size(){ return refine_data.size(); } // KE: stub, todo
  
  bool process_solver_result(); // KE: will call to SAT/UNSAT process result per expression
private:
  const optionst &options; 
  smtcheck_opensmt2t &decider; // Current support: LRA and UF
  bool is_lattice_ref_on;
  unsigned refineTryNum;

  /* Function declaration, head of the model - it is a map to support many models */
  std::map<std::string, lattice_refiner_modelt *> models; // Declare of func + its model
  std::map<std::string, SymRef> declare2literal; // Needed only for refine what openSMT can't express
  std::map<exprt, deque<lattice_refiner_modelt *>> refine_data; // Keep per expression, next options to refine
  // Top is what we use currently to refine the expression
  
  void load_models(std::string list_of_models_fs); // Load all the models
  
  // parent(s), current, siblings - walk on the lattice
  bool process_SAT_result(const exprt &expr);
  bool process_UNSAT_result(const exprt &expr);
  lattice_refiner_modelt* get_refine_function(const exprt &expr);
  
  bool can_refine(const smtcheck_opensmt2t &decider, 
                  const symex_assertion_sumt& symex) const;
  literalt refine_single_statement(const exprt &expr, const PTRef var);
  SymRef get_entry_point(const exprt &expr);
  std::string gen_entry_point_name(const exprt &expr);
};

#endif /* LATTICE_REFINERT_H */