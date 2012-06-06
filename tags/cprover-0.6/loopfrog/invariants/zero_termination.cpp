/*******************************************************************\

 Module: A string zero-termination invariant

 Author: CM Wintersteiger

\*******************************************************************/

#include <ansi-c/expr2c.h>
#include <ansi-c/c_types.h>
#include <std_expr.h>
#include <expr_util.h>
#include <goto-programs/string_abstraction.h>

#include "string_utils.h"

#include "zero_termination.h"

/*******************************************************************\
 
 Function: zero_termination_invariant_testt::get_invariants

 Inputs:

 Outputs:

 Purpose: Tests for zero termination preservation

\*******************************************************************/

void zero_termination_invariant_testt::get_invariants(
  const loop_summaryt &summary,
  std::set<exprt> &potential_invariants)  
{
  namespacet ns(context);
  
  stream_message_handlert mh(std::cout);
  string_abstractiont abs(context, mh);
     
  std::list<exprt> pointers;
  
  // find some strings
  for(std::set<exprt>::const_iterator it=summary.variant.begin();
      it!=summary.variant.end();
      it++)
  {    
    if(is_string_type(ns.follow(it->type())))
    {      
//      std::cout << expr2c(abs.is_zero_string(*it, false, locationt()), ns) << std::endl;
//      std::cout << *it << std::endl;
      pointers.push_back(*it);
    }
    else if(it->id()=="index")
    {      
      if(is_string_type(ns.follow(it->op0().type())))
      {
//        std::cout << expr2c(abs.buffer_termination(it->op0(), locationt()), ns) << std::endl;
//        std::cout << it->op0() << std::endl;
        pointers.push_back(it->op0());
      }
    }
  }
  
  // test the invariant for every string
  for(std::list<exprt>::const_iterator it = pointers.begin();
      it!=pointers.end();
      it++)
  {
    #if 0
    std::cout << "ZT TEST: " << expr2c(*it, ns) << std::endl;
    #endif
    
    exprt temp = *it;
    if(ns.follow(it->type()).id()=="array")
    {
      index_exprt array_0;
      array_0.array()=temp;
      array_0.index()=gen_zero(uint_type());
      exprt aof = address_of_exprt(array_0);
      temp.swap(aof);
    }
    
    exprt invariant = abs.is_zero_string(temp, false, locationt());
    
    if(invariant.op0().id()=="dereference" &&
       invariant.op0().op0().id()=="constant" &&
       invariant.op0().op0().get("value")=="NULL") continue; // not necessary...
    
    potential_invariants.insert(invariant);
    
    #if 0
    std::cout << "ZT INVARIANT: " << expr2c(invariant, ns) << std::endl;
    #endif
  }
}
