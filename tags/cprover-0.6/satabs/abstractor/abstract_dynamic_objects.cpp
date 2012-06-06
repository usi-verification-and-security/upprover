/*******************************************************************\

Module: Pointer Dereferencing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <i2string.h>
#include <std_expr.h>

#include "abstract_dynamic_objects.h"

/*******************************************************************\

Function: abstract_dynamic_objectst::collect

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void abstract_dynamic_objectst::collect(const exprt &expr)
{
  forall_operands(it, expr)
    collect(*it);
  
  if(expr.id()==ID_dereference)
  {
    assert(expr.operands().size()==1);
    ptr_set.insert(expr.op0());
  }
}

/*******************************************************************\

Function: abstract_dynamic_objectst::replace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void abstract_dynamic_objectst::replace(exprt &expr)
{
  Forall_operands(it, expr)
    replace(*it);
  
  if(expr.id()==ID_dereference)
  {
    assert(expr.operands().size()==1);
    expr=build_case_split(expr.op0());
  }
}

/*******************************************************************\

Function: abstract_dynamic_objectst::build_case_split

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt abstract_dynamic_objectst::build_case_split(const exprt &pointer)
{
  exprt result;
  
  result.make_nil();
  
  unsigned cnt=0;

  for(ptr_sett::const_iterator it=ptr_set.begin();
      it!=ptr_set.end();
      it++, cnt++)
  {
    if(pointer.type()!=it->type())
      continue;

    exprt value(ID_symbol, it->type().subtype());
    value.set(ID_identifier, "satabs::dynamic_object"+i2string(cnt));
  
    if(pointer==*it)
    {
      result=value;
    }
    else if(result.is_nil())
    {
      result=value;
    }
    else
    {
      equality_exprt ptr_equality;
      ptr_equality.lhs()=pointer;
      ptr_equality.rhs()=*it;
    
      if_exprt cond;
      cond.type()=pointer.type().subtype();
      cond.cond()=ptr_equality;
      cond.true_case()=value;
      cond.false_case()=result;
      
      result.swap(cond);
    }
  }
  
  assert(result.is_not_nil());
  
  return result;
}

