/*******************************************************************\

Module: Symex target equation which tracks different partitions for
different deferred functions.

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_SMT_PARTITIONING_TARGET_EQUATION_H
#define CPROVER_SMT_PARTITIONING_TARGET_EQUATION_H

#include "partitioning_target_equation.h"

class smtcheck_opensmt2t;
class interpolating_solvert;

// Two classes for smt and prop   
class smt_partitioning_target_equationt:public partitioning_target_equationt
{
public:
  smt_partitioning_target_equationt(const namespacet &_ns, summary_storet & store,
          bool _store_summaries_with_assertion)
            : partitioning_target_equationt(_ns, store,
                       _store_summaries_with_assertion) {}



};
#endif
