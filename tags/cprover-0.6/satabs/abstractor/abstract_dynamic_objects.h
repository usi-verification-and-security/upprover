/*******************************************************************\

Module: Pointer Dereferencing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SATABS_ABSTRACT_DYNAMIC_OBJECTS_H
#define CPROVER_SATABS_ABSTRACT_DYNAMIC_OBJECTS_H

#include <expr.h>
#include <hash_cont.h>

class abstract_dynamic_objectst
{
public:
  void collect(const exprt &expr);
  
  void replace(exprt &expr);
  
protected:
  typedef hash_set_cont<exprt, irep_hash> ptr_sett;
  ptr_sett ptr_set;
  
  exprt build_case_split(const exprt &ptr);
};

#endif
