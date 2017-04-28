/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   smt_assertion_no_partition.h
 * Author: karinek
 *
 * Created on 27 April 2017, 10:56
 */

#ifndef SMT_ASSERTION_NO_PARTITION_H
#define SMT_ASSERTION_NO_PARTITION_H

#include <namespace.h>
#include <ui_message.h>
#include <time_stopping.h>
#include <fstream>
#include <util/threeval.h>

#include "../assertion_info.h"
#include "smt_symex_target_equation.h"

extern time_periodt global_satsolver_time;

class smt_assertion_no_partitiont:public messaget 
{
    
public:
    smt_assertion_no_partitiont(
            smt_symex_target_equationt &_target,
            ui_message_handlert &_message_handler,
            unsigned long &_max_memory_used) 
        : equation(_target),
          solving_time(0),
          message_handler (_message_handler),
          max_memory_used(_max_memory_used)
          {set_message_handler(_message_handler);}
        
    virtual ~smt_assertion_no_partitiont() {}    
          
    bool assertion_holds(smtcheck_opensmt2t& decider);

    void error_trace(smtcheck_opensmt2t& decider, const namespacet &ns, std::map<irep_idt, std::string>& guard_expln);

private:
    // Store for the symex result
    smt_symex_target_equationt &equation;
    
    bool is_satisfiable(smtcheck_opensmt2t& decider);
    
    // SAT solving time
    time_periodt solving_time;

    ui_message_handlert &message_handler;

    unsigned long &max_memory_used;
};

#endif /* SMT_ASSERTION_NO_PARTITION_H */

