/*******************************************************************\

Module: Refiner

Author: Daniel Kroening

Date: September 2005

Purpose: Calculate predicates for predicate abstraction using
         Ken's Interpolating Prover

\*******************************************************************/

#ifndef CPROVER_SATABS_REFINER_IPP_H
#define CPROVER_SATABS_REFINER_IPP_H

#include "refiner_wp.h"

class refiner_ippt:public refiner_wpt
{
private:
  int limit;

public:
  refiner_ippt(const argst &args, bool _prefix_first, int _limit):
    refiner_wpt(args, _prefix_first),
    limit(_limit)
  {
  }

protected:
  bool refine_prefix(
    predicatest &predicates, 
    abstract_modelt &abstract_model,
    const fail_infot &fail_info);
};

#endif
