/*******************************************************************\

 Module: A pointer offset invariant

 Author: CM Wintersteiger

\*******************************************************************/

#include <ansi-c/expr2c.h>
#include <ansi-c/c_types.h>
#include <std_expr.h>
#include <expr_util.h>
#include <goto-programs/string_abstraction.h>

#include "pointer_expr.h"
#include "string_utils.h"

#include "pointer_offset.h"

/*******************************************************************\
 
 Function: pointer_offset_invariant_testt::get_invariants

 Inputs:

 Outputs:

 Purpose: Tests for non-NULL pointer preservation

\*******************************************************************/

void pointer_offset_invariant_testt::get_invariants(
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
    std::cout << "POFF TEST: " << expr2c(*it, ns) << std::endl;
    #endif
    
    typecast_exprt bufsize(int_type());
    bufsize.op()=abs.buffer_size(*it, locationt()); 
    
    pointer_offset_exprt pos(*it);
    binary_relation_exprt zero_lte_pos(gen_zero(int_type()), "<=", pos);
    binary_relation_exprt pos_lte_bufsize(pos, "<=", bufsize);
        
    and_exprt invariant(zero_lte_pos, pos_lte_bufsize);
    
    potential_invariants.insert(invariant);
    
    #if 0
    std::cout << "POFF INVARIANT: " << expr2c(invariant, ns) << std::endl;
    #endif
  }
}
