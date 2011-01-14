/*******************************************************************\

Module: Relations between variables

Author: CM Wintersteiger

\*******************************************************************/

#include <find_symbols.h>

#include "variable_relations_base.h"

/*******************************************************************\
 
 Function: variable_relations_invariant_testt::get_invariants

 Inputs:

 Outputs:

 Purpose: Tests for possible relations

 \*******************************************************************/

void variable_relations_invariant_testt::get_invariants(
  const loop_summaryt &summary,
  std::set<exprt> &potential_invariants)
{
  namespacet ns(context);

  std::set<exprt> symbols;
  
  for (std::set<exprt>::const_iterator it=summary.variant.begin(); 
       it!=summary.variant.end(); 
       it++)
    find_symbols(*it, symbols);
    
  std::set<exprt>::const_iterator ait=symbols.begin();
  std::set<exprt>::const_iterator bit=symbols.begin(); bit++;
  
  while(ait!=symbols.end() && bit!=symbols.end())
  {
    if(*ait!=*bit && ait->type() == bit->type())
    {
      binary_relation_exprt invariant(*ait, op, *bit);
      potential_invariants.insert(invariant);
      
      #if 0
      std::cout << "REL INVARIANT: " << expr2c(invariant, ns) << std::endl;
      #endif
    }
      
    bit++;
    
    if(bit==symbols.end()) { bit=++ait; bit++; }
  }
}
