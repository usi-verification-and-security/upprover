#ifndef SATISFYINGASSIGNMENT_H
#define SATISFYINGASSIGNMENT_H

#include "../solvers/smtcheck_opensmt2.h"
#include <util/expr.h>
#include <memory>

// List of current factories
class SatisfyingAssignmentCProverFactoryt;

// FIXME: change exprt into PTRef data
class SatisfyingAssignmentt {
public:
    virtual ~SatisfyingAssignmentt() {}
    
    std::map<const exprt, int>& get_model() { return m_model; }
    // std::map<const PTRef, int>& get_model() { return m_model; }

    // List of Factory classes per framework we support:
    friend class SatisfyingAssignmentCProverFactoryt;
    
private:
    std::map<const exprt, int> m_model;
    // std::map<const PTRef, int> m_model;
    
    SatisfyingAssignmentt(std::map<const exprt, int>& model) 
    // SatisfyingAssignmentt(std::map<const PTRef, int>& model) 
        : m_model(model) { }
}; // End of SatisfyingAssignmentt Class


/*********************************/
/*                               */
/* Frameworks Specific Factories */
/*                               */
/*********************************/
// GOTO-CC framework
class SatisfyingAssignmentCProverFactoryt {
public:
    std::unique_ptr<SatisfyingAssignmentt> getSatisfyingAssignment(
        smtcheck_opensmt2t &_decider, 
        std::vector<exprt>& exprs)
    {
        build_satisfying_assignment(exprs);
        return std::unique_ptr<SatisfyingAssignmentt>(new SatisfyingAssignmentt(m_model));
    }

private:
    std::map<const exprt, int> m_model;
    smtcheck_opensmt2t* decider;
            
    void build_satisfying_assignment(std::vector<exprt>& exprs);
    
    void get_vars_in_expr(exprt& e, std::set<exprt>& vars);
}; // End of SatisfyingAssignmentCProverFactoryt class
#endif /* SATISFYINGASSIGNMENT_H */

