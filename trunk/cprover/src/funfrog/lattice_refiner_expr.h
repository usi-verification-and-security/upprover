/* 
 * File:   lattice_refiner_expr.h
 * Author: karinek
 *
 * Created on 13 August 2017, 20:09
 */

#ifndef LATTICE_REFINER_EXPR_H
#define LATTICE_REFINER_EXPR_H

#include <expr.h>
#include <opensmt/opensmt2.h>
#include <source_location.h>
#include "lattice_refiner_model.h"
#include "solvers/smtcheck_opensmt2.h"
#include "symex_assertion_sum.h"


class lattice_refiner_exprt {
public:
    // C'tor for items with no declartion/body in the SSA parsing stage
    lattice_refiner_exprt(
            lattice_refiner_modelt *_head, 
            const exprt &_lhs, 
            const PTRef _lhs_ptref,
            const exprt::operandst &_call_info_operands,
            const std::string _refined_function,
            const source_locationt &_location) : 
        lhs(_lhs),
        lhs_PTRef(_lhs_ptref),
        call_info_operands(_call_info_operands),
        m_is_SAT(false),
        refined_function(_refined_function),
        location(_location)
        { refine_data.push_front(_head);}
        
    virtual ~lattice_refiner_exprt() { refine_data.clear(); refined_data_UNSAT.clear();}

    set<lattice_refiner_modelt*> get_refine_functions(); // refine_data.front(), TODO: Add the path here
    bool is_SAT() { return m_is_SAT;}
    bool is_UNSAT() { return !m_is_SAT && refine_data.empty() && !refined_data_UNSAT.empty();}
    
    void process_SAT_result();
    void process_UNSAT_result();

    std::string print_expr(smtcheck_opensmt2t &decider);
    
    // Not safe
    unsigned get_location() { return ((location.get_line().empty()) ? 0 : atoi(location.get_line().c_str()));}
    
    // basic data to build the assumes later
    const exprt& get_lhs();    
    const exprt::operandst& get_call_info_operands() { return call_info_operands;}
    const source_locationt& get_source_location() { return location;}

    void add_instantiated_fact(const irep_idt& fact_symbol) 
    { instantiated_facts.insert(fact_symbol);}
    
    bool is_fact_instantiated(const irep_idt& fact_symbol) 
    { return instantiated_facts.find(fact_symbol) != instantiated_facts.end(); }
private:
    // Currently node in use in the lattice: refine_data.front()
    const exprt& lhs;
    const PTRef lhs_PTRef;
    const exprt::operandst &call_info_operands; // rhs part 
    bool m_is_SAT; // Will be true if one of the paths in the lattice ends with SAT evaluation
    const std::string refined_function;
    const source_locationt& location;
    std::set<irep_idt> instantiated_facts;
    
    std::deque<lattice_refiner_modelt *> refine_data; // Next nodes in the lattice to use for refining this expression
    std::set<lattice_refiner_modelt *> refined_data_UNSAT; // Paths that ended in UNSAT (if all ended in UNSAT => UNSAT) + bot is here!
    
    void remove_dequed_data(lattice_refiner_modelt *curr); // Remove from refine_data all nodes with paths only to UNSAT nodes.
    const std::set<irep_idt>& pop_facts_ids(lattice_refiner_modelt *curr); // Remove from the instantite facts, all the facts that aren't in use (go backward)
    bool is_all_childs_leads_to_UNSAT(lattice_refiner_modelt *curr);
};
    
#endif /* LATTICE_REFINER_EXPR_H */