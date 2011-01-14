/*******************************************************************\

 Module: An iterator bounds invariant

 Author: CM Wintersteiger

\*******************************************************************/

#include <ansi-c/expr2c.h>
#include <ansi-c/c_types.h>
#include <std_expr.h>
#include <expr_util.h>
#include <goto-programs/string_abstraction.h>

#include "string_utils.h"

#include "iterator_bounds.h"

/*******************************************************************\
 
 Function: iterator_bounds_invariant_testt::find_indexes

 Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void iterator_bounds_invariant_testt::find_indexes(
  const exprt &expr,
  std::set<exprt> &to) const
{
  if(expr.id()=="index")
  {      
    const exprt &array = expr.op0();
    
    if (array.id()=="symbol" ||
        array.id()==ID_string_constant)
    {
      const typet &type = ns.follow(array.type());
      
      if(type.id()=="array" &&
         is_char_type(type.subtype()))          
        to.insert(expr);
    }
  }
  else
    forall_operands(it, expr)
      find_indexes(*it, to);
}

/*******************************************************************\
 
 Function: iterator_bounds_invariant_testt::find_indexes

 Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void iterator_bounds_invariant_testt::find_indexes(
  const std::set<exprt> &from,
  std::set<exprt> &to) const
{
  for(std::set<exprt>::const_iterator it=from.begin();
      it!=from.end();
      it++)
  {    
    find_indexes(*it, to);
  } 
}

/*******************************************************************\
 
 Function: iterator_bounds_invariant_testt::get_invariants

 Inputs:

 Outputs:

 Purpose: Tests for iterator bounds

\*******************************************************************/

void iterator_bounds_invariant_testt::get_invariants(
  const loop_summaryt &summary,
  std::set<exprt> &potential_invariants)  
{
  stream_message_handlert mh(std::cout);
  string_abstractiont abs(context, mh);
     
  std::set<exprt> indexes;
  
  find_indexes(summary.variant, indexes);
  find_indexes(summary.rhs_expressions, indexes);
  
  if(indexes.size()>3) return; // give up on big loops
  
  // test the invariant for every index and it's iterator
  for(std::set<exprt>::const_iterator it = indexes.begin();
      it!=indexes.end();
      it++)
  {
    #if 0
    std::cout << "IB TEST: " << expr2c(*it, ns) << std::endl;
    #endif
    
    const index_exprt index_e = to_index_expr(*it);
    const exprt array = index_e.array();
    const exprt index = index_e.index();
    const typet array_type = ns.follow(array.type());
    exprt buffer_size = to_array_type(array_type).size();
    
    if(buffer_size.type().id()!=index.type().id())
      buffer_size.make_typecast(index.type());
    
    binary_relation_exprt zero_lte_it(gen_zero(index.type()), "<=", index);
    binary_relation_exprt it_lt_bsize(index, "<", buffer_size);
    
    and_exprt invariant(zero_lte_it, it_lt_bsize);
    
    potential_invariants.insert(invariant);
    
    #if 0
    std::cout << "IB INVARIANT: " << expr2c(invariant, ns) << std::endl;
    #endif
  }
}
