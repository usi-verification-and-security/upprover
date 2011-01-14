/*******************************************************************

 Module: Adaptor for value sets (state duplication)

 Author: CM Wintersteiger

\*******************************************************************/

#ifndef _CPROVER_LOOPFORG_VALUE_SET_DUPLICATION_ADAPTOR_H_
#define _CPROVER_LOOPFORG_VALUE_SET_DUPLICATION_ADAPTOR_H_

#include <map>

#include <context.h>
#include <pointer-analysis/value_sets.h>

class value_set_duplication_adaptort : public value_setst
{
private:
  value_setst &value_sets;
  
  typedef std::map<goto_programt::const_targett, 
                   goto_programt::const_targett> duplicationt;
                   
  duplicationt duplication;

public:  
  value_set_duplication_adaptort(
    value_setst &_value_sets) :
      value_sets(_value_sets) {};
  
  virtual void get_values(
    goto_programt::const_targett l,
    const exprt &expr,
    valuest &dest);
  
  void duplicate(
    goto_programt::const_targett existing_state,
    goto_programt::const_targett duplicate)
  {
    duplication[duplicate] = existing_state;
  }
};

#endif /*_CPROVER_LOOPFORG_VALUE_SET_ALLOC_ADAPTOR_H_*/
