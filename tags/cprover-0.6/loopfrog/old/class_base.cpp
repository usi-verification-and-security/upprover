/*******************************************************************\
 
Module: loop classification for Loopfrog: classification class base class
 
Author: Daniel Kroening
        CM Wintersteiger
 
Date: June 2007
 
\*******************************************************************/

#include <fstream>

#include "class_base.h"

/*******************************************************************\
 
Function: class_baset::classify
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/
bool class_baset::classify( 
  const contextt& context,
  const goto_programt& program,
  goto_programt::const_targett &begin,
  goto_programt::const_targett &end)
{
  bool res = recognize(context, program, begin, end);
  if (res) recognized++;
  return res;
}

/*******************************************************************\
 
Function: class_baset::report
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/
void class_baset::report( std::ostream& )
{
}

/*******************************************************************\
 
Function: class_baset::save_loop
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/
void class_baset::save_loop( 
  const std::string &filename,
  const contextt &context,         
  const goto_programt &program, 
  goto_programt::const_targett &begin,
  goto_programt::const_targett &end) const
{
  std::ofstream f(filename.c_str(), std::ios::app);
  f << "----------------------" << std::endl;
  namespacet ns(context);
  goto_programt::const_targett i=begin;
  do
  {      
    program.output_instruction(ns, "", f, i);
  } while(i++!=end);    
  f << std::endl;
  f.close();  
}
