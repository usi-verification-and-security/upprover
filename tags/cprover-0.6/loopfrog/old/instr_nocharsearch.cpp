/*******************************************************************\
 
Module: loop instrumentation for Loopfrog: nocharsearch class
 
Author: Daniel Kroening
        CM Wintersteiger
        Aliaksei Tsitovich
 
Date: June 2007
 
\*******************************************************************/

#include <fstream>

#include "instr_nocharsearch.h"

/*******************************************************************\
 
Function: instr_nocharsearcht::instrument
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/
bool instr_nocharsearcht::instrument( 
  contextt& context,
  goto_programt& program, 
  goto_programt::targett &begin,
  goto_programt::targett &end)
{  
  return false;
}
