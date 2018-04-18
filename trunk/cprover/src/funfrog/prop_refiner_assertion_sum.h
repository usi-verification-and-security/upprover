#ifndef PROP_REFINER_ASSERTION_SUMT_H
#define PROP_REFINER_ASSERTION_SUMT_H

#include "refiner_assertion_sum.h"


class prop_partitioning_target_equationt;
class prop_conv_solvert;

class prop_refiner_assertion_sumt : public refiner_assertion_sumt 
{
public:
    prop_refiner_assertion_sumt(
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

          virtual ~prop_refiner_assertion_sumt() {}

    void refine(const prop_conv_solvert &decider, call_tree_nodet& summary, prop_partitioning_target_equationt &equation);
  
protected:
    void reset_depend(const prop_conv_solvert &decider, call_tree_nodet& summary, prop_partitioning_target_equationt &equation);
  
};

#endif /* PROP_REFINER_ASSERTION_SUMT_H */

