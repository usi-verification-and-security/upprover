#ifndef PROP_ASSERTION_SUM_H
#define PROP_ASSERTION_SUM_H

#include "assertion_sum.h"


class assertion_infot;
class prop_partitioning_target_equationt;
class prop_conv_solvert;
class interpolating_solvert;
class namespacet;
class decision_proceduret;

class prop_assertion_sumt : public messaget
{
public:
    prop_assertion_sumt(
            prop_partitioning_target_equationt &_target,
            ui_message_handlert &_message_handler
            )
        : messaget(_message_handler),
          equation(_target) {};
      
    virtual ~prop_assertion_sumt() {}
    
    bool assertion_holds(const assertion_infot &assertion, const namespacet &ns, prop_conv_solvert& decider, interpolating_solvert& interpolator);

    void error_trace(const prop_conv_solvert &prop_conv, const namespacet &ns);

private:
    // Store for the symex result
    prop_partitioning_target_equationt &equation;
    
    bool is_satisfiable(decision_proceduret &decision_procedure);
};

#endif /* PROP_ASSERTION_SUM_H */

