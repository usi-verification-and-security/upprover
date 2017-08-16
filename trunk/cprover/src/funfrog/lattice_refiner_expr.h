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
#include "lattice_refiner_model.h"
#include "solvers/smtcheck_opensmt2.h"

class lattice_refiner_exprt {
public:
    // C'tor for items with no declartion/body in the SSA parsing stage
    lattice_refiner_exprt(
            lattice_refiner_modelt *_head, 
            const exprt &_lhs, 
            const PTRef _lhs_ptref,
            const exprt::operandst &_call_info_operands,
            const std::string _refined_function) : 
        lhs(_lhs),
        lhs_PTRef(_lhs_ptref),
        call_info_operands(_call_info_operands),
        m_is_SAT(false),
        refined_function(_refined_function)        
        { refine_data.push_front(_head);}
        
    virtual ~lattice_refiner_exprt() { refine_data.clear(); refined_data_UNSAT.clear();}

    set<lattice_refiner_modelt*> get_refine_functions(); // refine_data.front(), TODO: Add the path here
    bool is_SAT() { return m_is_SAT;}
    bool is_UNSAT() { return !m_is_SAT && refine_data.empty() && !refined_data_UNSAT.empty();}
    
    void process_SAT_result();
    void process_UNSAT_result();

    std::string print_expr(smtcheck_opensmt2t &decider);

private:
    // Currently node in use in the lattice: refine_data.front()
    const exprt& lhs;
    const PTRef lhs_PTRef;
    const exprt::operandst &call_info_operands; // rhs part 
    bool m_is_SAT; // Will be true if one of the paths in the lattice ends with SAT evaluation
    const std::string refined_function;
    
    std::deque<lattice_refiner_modelt *> refine_data; // Next nodes in the lattice to use for refining this expression
    std::set<lattice_refiner_modelt *> refined_data_UNSAT; // Paths that ended in UNSAT (if all ended in UNSAT => UNSAT) + bot is here!
    
    void remove_dequed_data(lattice_refiner_modelt *curr); // Remove from refine_data all nodes with paths only to UNSAT nodes.
    bool is_all_childs_leads_to_UNSAT(lattice_refiner_modelt *curr);
};
    
#endif /* LATTICE_REFINER_EXPR_H */