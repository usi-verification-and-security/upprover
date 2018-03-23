#ifndef REFINER_H
#define REFINER_H

#include "SatisfyingAssignment.h"

/*
 * This class is a general interface for refinement
 * 
 * extended by: 
 *      SummaryRefiner, TheoryRefiner, LatticeRefiner
 * 
 */
class Refinert {
public:
    Refinert(){}
    virtual ~Refinert() {}
    
    // Refine the current representation
    bool refine()=0;
    
    // Check if a counter example is spurious
    bool check_spurious(SatisfyingAssignmentt cex)=0;
    
protected:
    // KE: not sure if it is in the refiner or in the main loop (after getting "true" from refine() methof
    // If refined - then need to update the smt formula
    void update_smt_formula()=0;
    
    // To refine, shall work according to a heuristic
    // int heuristic: shall be enum
    // To replace: std::vector<exprt>& get_exprs_to_refine () method
    std::vector<exprt>& get_expr_refine_order_heuristic(int heuristic)=0;
};

#endif /* REFINER_H */

