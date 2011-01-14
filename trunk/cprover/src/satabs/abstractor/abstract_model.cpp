/*******************************************************************\

Module: Abstract Program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include "abstract_model.h"

/*******************************************************************\

Function: abstract_modelt::get_abstract_location

  Inputs:

 Outputs:

 Purpose: given a concrete location, returns the appropriate
          abstract one

\*******************************************************************/

abstract_programt::targett abstract_modelt::get_abstract_location(
  goto_programt::const_targett concrete_location)
{
  for(abstract_functionst::function_mapt::iterator 
      f_it=goto_functions.function_map.begin();
      f_it!=goto_functions.function_map.end();
      f_it++)
  {
    for(abstract_programt::instructionst::iterator
        i_it=f_it->second.body.instructions.begin();
        i_it!=f_it->second.body.instructions.end();
        i_it++)
    {
      if(i_it->code.concrete_pc==concrete_location)
        return i_it;
    }
  }

  assert(0);
}

