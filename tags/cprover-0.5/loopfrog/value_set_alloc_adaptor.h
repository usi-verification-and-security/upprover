/*******************************************************************

 Module: Adaptor for value sets (dynamic object removal)

 Author: CM Wintersteiger

\*******************************************************************/

#ifndef _CPROVER_LOOPFORG_VALUE_SET_ALLOC_ADAPTOR_H_
#define _CPROVER_LOOPFORG_VALUE_SET_ALLOC_ADAPTOR_H_

#include <expr_util.h>
#include <context.h>
#include <pointer-analysis/value_sets.h>

class value_set_alloc_adaptort : public value_setst
{
private:
  contextt &context;
  value_setst &value_sets;

public:
  value_set_alloc_adaptort(
    contextt &_context,
    value_setst &_value_sets) :
      context(_context),
      value_sets(_value_sets) {};

  virtual void get_values(
      goto_programt::const_targett l,
      const exprt &expr,
      valuest &dest);

private:
  void replace_dynamic_objects(exprt &expr);
};

#endif /*_CPROVER_LOOPFORG_VALUE_SET_ALLOC_ADAPTOR_H_*/
