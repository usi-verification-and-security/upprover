/*******************************************************************

 Module: Adaptor for invariant propagation to prove claims in Loopfrog

 Author: A. Tsitovich

\*******************************************************************/

#ifndef _CPROVER_LOOPFORG_INVARIANT_PROPAGATION_ADAPTOR_H_
#define _CPROVER_LOOPFORG_INVARIANT_PROPAGATION_ADAPTOR_H_

#include <goto-programs/invariant_propagation.h>

class invariant_propagation_adaptort : public invariant_propagationt
{
public:
  invariant_propagation_adaptort(
    const namespacet &_ns,
    value_setst &_value_sets):
      invariant_propagationt(_ns, _value_sets)
  {
  }

  bool implies_claim(goto_programt::targett &i_it) const;
};

#endif /*_CPROVER_LOOPFORG_INVARIANT_PROPAGATION_ADAPTOR_H_*/
