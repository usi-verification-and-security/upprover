/*******************************************************************\

 Module: A pointer object invariant

 Author: CM Wintersteiger

\*******************************************************************/

#include <ansi-c/expr2c.h>
#include <ansi-c/c_types.h>
#include <std_expr.h>
#include <expr_util.h>
#include <goto-programs/string_abstraction.h>

#include "pointer_expr.h"
#include "string_utils.h"

#include "pointer_object.h"

/*******************************************************************\

 Function: pointer_object_invariant_testt::get_invariants

 Inputs:

 Outputs:

 Purpose: Tests for preservation of the string tracker structure

\*******************************************************************/

void pointer_object_invariant_testt::get_invariants(
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
    std::cout << "PO TEST: " << expr2c(*it, ns) << std::endl;
    #endif

    symbol_exprt temp = get_temporary_symbol(uint_type());
    
    exprt pobj("pointer_object", uint_type());
    pobj.copy_to_operands(*it);    

    binary_relation_exprt invariant(temp, "=", pobj);
    invariant.set("#unconditional", true);

    potential_invariants.insert(invariant);

    #if 0
    std::cout << "PO INVARIANT: " << expr2c(invariant, ns) << std::endl;
    #endif
  }
}
