/*******************************************************************\

Module: Transition Cache

Author: Daniel Kroening
    
Date: October 2005

Purpose:

\*******************************************************************/

#ifndef CPROVER_SATABS_REFINER_TRANSITION_CACHE_H
#define CPROVER_SATABS_REFINER_TRANSITION_CACHE_H

#include "../modelchecker/abstract_counterexample.h"

class transition_cachet
{
public:
  typedef std::map<unsigned, bool> valuest;

  struct entryt
  {
    goto_programt::const_targett pc;
    valuest from, to;

    friend bool operator==(
      const entryt &a,
      const entryt &b)
    {
      if(a.pc!=b.pc)
        return false;
      
      return a.from==b.from && a.to==b.to;
    }
    
    void build(
      const abstract_stept &abstract_state_from,
      const abstract_stept &abstract_state_to);
  };

  struct entry_hasht
  {
    size_t operator()(const entryt &e) const
    {
      return ((unsigned long)&(*e.pc))^e.from.size()^e.to.size();
    }
  };
  
  typedef hash_set_cont<entryt, entry_hasht> cachet;
  cachet cache;

  bool in_cache(const entryt &entry)
  {
    return cache.find(entry)!=cache.end();
  }
  
  void insert(const entryt &entry)
  {
    cache.insert(entry);
  }
};

#endif
