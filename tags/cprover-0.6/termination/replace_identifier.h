/*******************************************************************\

Module: 

Author: CM Wintersteiger

\*******************************************************************/

#ifndef CPROVER_SATABS_TERMINATION_REPLACE_IDENTIFIER_H_
#define CPROVER_SATABS_TERMINATION_REPLACE_IDENTIFIER_H_

#include "hash_cont.h"
#include "expr.h"
#include "type.h"

class replace_idt : public hash_map_cont<irep_idt, irep_idt, irep_id_hash>
{
public:
  void insert(const irep_idt &before, const irep_idt &after)
  {
    operator[](before)=after;
  }
  
  bool replace(exprt &expr) const;
  bool replace(typet &type) const;
};

#endif
