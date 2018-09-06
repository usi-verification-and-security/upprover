/*******************************************************************
 * File:   smt_assertion_no_partition.h
 * Author: karinek
 * Created on 27 April 2017
 *******************************************************************/

#ifndef SMT_ASSERTION_NO_PARTITION_H
#define SMT_ASSERTION_NO_PARTITION_H

#include <util/namespace.h>
#include <util/ui_message.h>
#include <util/time_stopping.h>
#include <util/threeval.h>

#include "../assertion_info.h"
#include "hifrog_symex_target_equation_no_partition.h"

class smtcheck_opensmt2;

extern time_periodt global_satsolver_time;

class smt_assertion_no_partitiont:public messaget 
{
    
public:
    smt_assertion_no_partitiont(
            hifrog_symex_target_equationt &_target,
            ui_message_handlert &_message_handler,
            unsigned long &_max_memory_used) 
        : equation(_target),
          solving_time(0),
          message_handler(_message_handler),
          max_memory_used(_max_memory_used)
          {set_message_handler(_message_handler);}

    using SSA_steps_orderingt = std::vector<symex_target_equationt::SSA_stept*>;

    virtual ~smt_assertion_no_partitiont() {}    
          
    bool assertion_holds(smtcheck_opensmt2t& decider);
   
    bool is_satisfiable(smtcheck_opensmt2t& decider); 

    void error_trace(smtcheck_opensmt2t& decider, const namespacet &ns, std::map<irep_idt, std::string>& guard_expln);
    
    const SSA_steps_orderingt get_steps_exec_order() {
        SSA_steps_orderingt ret; ret.reserve(equation.SSA_steps.size());
        for(symex_target_equationt::SSA_stepst::iterator it=equation.SSA_steps.begin(); it!=equation.SSA_steps.end(); it++)
            ret.push_back(&*it);;
        return ret;
    }

    // Store for the symex result
    hifrog_symex_target_equationt &equation;
    
    // SAT solving time
    time_periodt solving_time;

    ui_message_handlert &message_handler;

    unsigned long &max_memory_used;
};
#endif /* SMT_ASSERTION_NO_PARTITION_H */

