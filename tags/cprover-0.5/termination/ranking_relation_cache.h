/*******************************************************************\

Module: Ranking relation cache 

Author: CM Wintersteiger

\*******************************************************************/

#ifndef RANKING_RELATION_CACHE_H_
#define RANKING_RELATION_CACHE_H_

#include <set>

#include <expr.h>
#include <message.h>
#include <namespace.h>
#include <std_expr.h>

#include "find_symbols_rw.h"
#include "replace_identifier.h"

class qdimacs_cnft;
class bv_pointerst;

class ranking_relation_cachet : public messaget
{  
private:
  const namespacet &ns;
  
  class cache_entryt { public: exprt relation; find_symbols_sett symbols; };  
  typedef std::vector<cache_entryt> ranking_relationst;
  ranking_relationst ranking_relations;
  
  exprt constraint;
  
public:  
  ranking_relation_cachet(const namespacet &_ns,
                          message_handlert &_mh) :
                            messaget(_mh),
                            ns(_ns),
                            hit(0),
                            miss(0) 
  {
    constraint.make_true();
  }
  
  unsigned hit, miss;
  
  bool is_ranked(const exprt &body);
  
  exprt disjunctive_relation(void) const;
  bool is_compositional(void);
  
  bool insert(const exprt &rr);  
  unsigned size(void) { return ranking_relations.size(); }
  void clear(void) { ranking_relations.clear(); }
  
  void add_constraint(const exprt &c) 
  { constraint = and_exprt(constraint, c); }
  const exprt &get_constraint(void) const { return constraint; }
  
protected:
  void get_pre_post(const std::set<exprt> &symbols, 
                    replace_idt &premap) const;
};

#endif
