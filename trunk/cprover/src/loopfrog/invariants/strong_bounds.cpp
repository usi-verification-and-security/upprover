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

#include "strong_bounds.h"

/*******************************************************************\
 
 Function: iterator_bounds_invariant_testt::find_indexes

 Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void strong_bounds_invariant_testt::find_indexes(
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

void strong_bounds_invariant_testt::find_indexes(
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
 
 Function: strong_bounds_invariant_testt::get_invariants

 Inputs:

 Outputs:

 Purpose: Tests for iterator bounds

\*******************************************************************/

void strong_bounds_invariant_testt::get_invariants(
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
    std::cout << "SB TEST: " << expr2c(*it, ns) << std::endl;
    #endif
    
    const index_exprt index_e = to_index_expr(*it);
    const exprt array = index_e.array();
    const exprt index = index_e.index();
    const typet array_type = ns.follow(array.type());
    const exprt buffer_size = to_array_type(array_type).size();        
        
    exprt temp = array;
    if(ns.follow(temp.type()).id()=="array")
    {
      index_exprt array_0;
      array_0.array()=temp;
      array_0.index()=gen_zero(uint_type());
      array_0.type()=array.type().subtype();
      exprt aof = address_of_exprt(array_0);
      temp.swap(aof);
    }
    exprt is_zero = abs.is_zero_string(temp, false, locationt());
    exprt strlen = abs.zero_string_length(temp, false, locationt());
    
    index_exprt zci;
    zci.type()=array_type.subtype();
    zci.array()=array;
    zci.index()=strlen;
    
    exprt uint_index(index);
    if(uint_index.type().id()!="unsignedbv")
      uint_index.make_typecast(uint_type());
    
    exprt int_strlen(strlen);
    int_strlen.make_typecast(int_type());
    
    exprt ubuffer_size(buffer_size);
    ubuffer_size.make_typecast(uint_type());
    
    binary_relation_exprt strlen_bound(strlen, "<", ubuffer_size);    
    
    binary_relation_exprt zero_lte_it(gen_zero(uint_type()), "<=", uint_index);
    binary_relation_exprt it_lt_bsize(uint_index, "<=", strlen);
    
    binary_relation_exprt zero_char(zci, "=", gen_zero(zci.type()));
    
    and_exprt invariant;
    invariant.move_to_operands(strlen_bound, zero_char);
    invariant.move_to_operands(zero_lte_it, it_lt_bsize);
    
    
    potential_invariants.insert(invariant);
    
    #if 0
    std::cout << "SB INVARIANT: " << expr2c(invariant, ns) << std::endl;
    #endif
  }
}
