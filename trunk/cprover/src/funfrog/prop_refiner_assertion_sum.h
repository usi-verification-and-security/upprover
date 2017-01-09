/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   prop_refiner_assertion_sumt.h
 * Author: karinek
 *
 * Created on 09 January 2017, 20:01
 */

#ifndef PROP_REFINER_ASSERTION_SUMT_H
#define PROP_REFINER_ASSERTION_SUMT_H

#define "refiner_assertion_sum.h"

class prop_refiner_assertion_sumt : refiner_assertion_sumt 
{
public:
    prop_refiner_assertion_sumt(
          summarization_contextt &_summarization_context,
          subst_scenariot &_omega,
          refinement_modet _mode,
          message_handlert &_message_handler,
          const unsigned _last_assertion_loc,
          bool _valid
          ) : refiner_assertion_sumt(_summarization_context,
          _omega, _mode, _message_handler, _last_assertion_loc,
          _valid)
          {}

          virtual ~refiner_assertion_sumt() {}

    void refine(const prop_conv_solvert &decider, summary_infot& summary, partitioning_target_equationt &equation);
  
protected:
    void reset_depend(const prop_conv_solvert &decider, summary_infot& summary, partitioning_target_equationt &equation);
  
};

#endif /* PROP_REFINER_ASSERTION_SUMT_H */

