/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   smt_refiner_assertion_sumt.h
 * Author: karinek
 *
 * Created on 09 January 2017, 19:57
 */

#ifndef SMT_REFINER_ASSERTION_SUMT_H
#define SMT_REFINER_ASSERTION_SUMT_H

#include "refiner_assertion_sum.h"

class smtcheck_opensmt2t;
class smt_partitioning_target_equationt;

class smt_refiner_assertion_sumt : public refiner_assertion_sumt 
{
public:
    smt_refiner_assertion_sumt(
          summary_storet & summary_store,
          subst_scenariot &_omega,
          refinement_modet _mode,
          message_handlert &_message_handler,
          const unsigned _last_assertion_loc,
          bool _valid
          ) : refiner_assertion_sumt(summary_store,
          _omega, _mode, _message_handler, _last_assertion_loc,
          _valid)
          {}

          virtual ~smt_refiner_assertion_sumt() {}
    
    void refine(const smtcheck_opensmt2t &decider, call_tree_nodet& summary, smt_partitioning_target_equationt &equation);
  
protected:
    void reset_depend(const smtcheck_opensmt2t &decider, call_tree_nodet& summary, smt_partitioning_target_equationt &equation);
    
};


#endif /* SMT_REFINER_ASSERTION_SUMT_H */

