/*
 * File:   smt_assertion_sum.h
 * Author: karinek
 *
 * Created on 10 January 2017, 16:30
 */

#ifndef SMT_ASSERTION_SUM_H
#define SMT_ASSERTION_SUM_H

#include <util/message.h>
#include <util/ui_message.h>

class assertion_infot;
class namespacet;
class smt_partitioning_target_equationt;
class smtcheck_opensmt2t;
class interpolating_solvert;

class prepare_smt_formulat :public messaget
{
public:
    prepare_smt_formulat(
            smt_partitioning_target_equationt &_target,
            ui_message_handlert &_message_handler
            )
        : messaget(_message_handler),
          equation(_target) {};
    
    void convert_to_formula(smtcheck_opensmt2t &decider,interpolating_solvert &interpolator);

    void error_trace(smtcheck_opensmt2t& decider, const namespacet &ns, std::map<irep_idt, std::string>& guard_expln);

    bool is_satisfiable(smtcheck_opensmt2t& decider);
private:
    // Store for the symex result
    smt_partitioning_target_equationt &equation;

};

#endif /* SMT_ASSERTION_SUM_H */

