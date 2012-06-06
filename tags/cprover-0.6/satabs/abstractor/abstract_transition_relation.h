/*******************************************************************\

Module: An Abstract Transition Relation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CEGAR_ABSTRACT_TRANS_H
#define CPROVER_CEGAR_ABSTRACT_TRANS_H

#include <set>
#include <list>

#include <expr.h>

class abstract_initial_statet
{
public:
  // for states that are *not* allowed
  typedef std::list<exprt> constraintst;
  constraintst constraints;
};

class abstract_transition_relationt
{
public:
  // predicate localization
  std::set<unsigned> from_predicates, to_predicates;
  
  bool has_predicates() const
  {
    return !from_predicates.empty() ||
           !to_predicates.empty() ||
           !values.empty();
  }

  // predicates with fixed values in terms of other predicates
  // nil = unconstrained
  // not im map = does not change
  typedef std::map<unsigned, exprt> valuest;
  valuest values;
  
  bool has_nondeterminism() const
  {
    for(valuest::const_iterator
        it=values.begin();
        it!=values.end();
        it++)
      if(it->second.is_nil())
        return true;
        
    return false;
  }

  bool is_skip() const
  {
    return values.empty();
  }

  // for transitions that are *not* allowed
  typedef std::list<exprt> constraintst;
  constraintst constraints;
  
  void clear()
  {
    constraints.clear();
    values.clear();
  }
  
  void swap(abstract_transition_relationt &abstract_transition_relation)
  {
    abstract_transition_relation.constraints.swap(constraints);
    abstract_transition_relation.values.swap(values);
  }
};

class abstract_transition_systemt
{
public:
  abstract_transition_relationt transition_relation;
  abstract_initial_statet initial_state;
  std::string description;
  
  typedef std::list<exprt> propertiest;
  propertiest properties;
  
  bool has_property() const
  {
    return !properties.empty();
  }
  
  void output(std::ostream &out) const
  {
  }
};
 
#endif
