/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   smt_assertion_sum.h
 * Author: karinek
 *
 * Created on 10 January 2017, 16:30
 */

#ifndef SMT_ASSERTION_SUM_H
#define SMT_ASSERTION_SUM_H

#include "assertion_sum.h"
#include "solvers/smtcheck_opensmt2.h"

class smt_assertion_sumt : public assertion_sumt 
{
public:
    smt_assertion_sumt(
            summarization_contextt& _summarization_context,
            smt_partitioning_target_equationt &_target,
            ui_message_handlert &_message_handler,
            unsigned long &_max_memory_used
            ) 
        : assertion_sumt(_summarization_context,
                        _message_handler, 
                        _max_memory_used), 
          equation(_target) {};
    
    bool assertion_holds(const assertion_infot &assertion, const namespacet &ns, smtcheck_opensmt2t& decider, interpolating_solvert& interpolator);

    void error_trace(smtcheck_opensmt2t& decider, const namespacet &ns, std::map<irep_idt, std::string>& guard_expln);

private:
    // Store for the symex result
    smt_partitioning_target_equationt &equation;
    
    bool is_satisfiable(smtcheck_opensmt2t& decider);
};

#endif /* SMT_ASSERTION_SUM_H */

