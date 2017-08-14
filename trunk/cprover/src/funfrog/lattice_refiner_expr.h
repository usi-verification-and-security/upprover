/* 
 * File:   lattice_refiner_expr.h
 * Author: karinek
 *
 * Created on 13 August 2017, 20:09
 */

#ifndef LATTICE_REFINER_EXPR_H
#define LATTICE_REFINER_EXPR_H

#include <expr.h>
#include <deque>
#include <set>
#include "lattice_refiner_model.h"

class lattice_refiner_exprt {
public:
    lattice_refiner_exprt(const exprt &_expr) : 
        expr(_expr), 
        m_is_SAT(false)
        {}
    virtual ~lattice_refiner_exprt() { refine_data.clear(); refined_data_UNSAT.clear();}

    lattice_refiner_modelt* get_refine_function(); // refine_data.front()
    bool is_SAT() { return m_is_SAT;}
    bool is_UNSAT() { return !m_is_SAT && refine_data.empty() && !refined_data_UNSAT.empty();}
    const exprt& get_expr() { return expr; }
    
    void process_SAT_result();
    void process_UNSAT_result();
    
private:
    // Currently node in use in the lattice: refine_data.front()
    const exprt& expr;
    bool m_is_SAT; // Will be true if one of the paths in the lattice ends with SAT evaluation
    
    std::deque<lattice_refiner_modelt *> refine_data; // Next nodes in the lattice to use for refining this expression
    std::set<lattice_refiner_modelt *> refined_data_UNSAT; // Paths that ended in UNSAT (if all ended in UNSAT => UNSAT)
    
    void remove_dequed_data(lattice_refiner_modelt *curr); // Remove from refine_data all nodes with paths only to UNSAT nodes.
    bool is_all_childs_leads_to_UNSAT(lattice_refiner_modelt *curr);
};
    
#endif /* LATTICE_REFINER_EXPR_H */