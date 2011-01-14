/*******************************************************************\

Module: Refiner

Author: Daniel Kroening

Date: December 2005

Purpose: Calculate predicates for predicate abstraction

\*******************************************************************/

#ifndef CPROVER_SATABS_TRANS_WP_H
#define CPROVER_SATABS_TRANS_WP_H

#include <trans/word_level_trans.h>

class trans_wpt:public word_level_transt
{
public:
  trans_wpt(const namespacet &_ns):
    word_level_transt(_ns)
  {
  }

  void wp(exprt &expr);
  
protected:
  void wp_rec(exprt &expr);
};

#endif
