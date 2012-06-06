/*******************************************************************\

 Module: A string length preservation invariant

 Author: CM Wintersteiger

\*******************************************************************/

#include <ansi-c/expr2c.h>
#include <ansi-c/c_types.h>
#include <std_expr.h>
#include <expr_util.h>
#include <goto-programs/string_abstraction.h>

#include "pointer_expr.h"
#include "string_utils.h"

#include "null_pointer.h"

/*******************************************************************\
 
 Function: null_pointer_invariant_testt::get_invariants

 Inputs:

 Outputs:

 Purpose: Tests for pointer offset validity preservation

\*******************************************************************/

void null_pointer_invariant_testt::get_invariants(
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
    if(it->type().id()=="pointer" &&
       is_char_type(it->type().subtype()))
    {      
      pointers.push_back(*it);
    }
  }
  
  // test the invariant for every string
  for(std::list<exprt>::const_iterator it = pointers.begin();
      it!=pointers.end();
      it++)
  {
    #if 0
    std::cout << "NP TEST: " << expr2c(*it, ns) << std::endl;
    #endif
    
    same_object_exprt invariant(*it, gen_zero(it->type()));
    invariant.make_not();
        
    potential_invariants.insert(invariant);
    
    #if 0
    std::cout << "NP INVARIANT: " << expr2c(invariant, ns) << std::endl;
    #endif
  }
}
