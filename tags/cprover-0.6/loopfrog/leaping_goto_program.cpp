/*******************************************************************\

Module: Leaping GOTO Program

Author: CM Wintersteiger

\*******************************************************************/

#include "leaping_goto_program.h"

/*******************************************************************\

Function: leaping_goto_programt::output_instruction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream& leaping_goto_programt::output_instruction(
  const class namespacet &ns,
  const irep_idt &identifier,
  std::ostream& out,
  instructionst::const_iterator it) const
{
  if(it->type==OTHER)
  {
    const codet &code = to_code(it->code);

    if(code.get_statement()=="loop-summary")
    {
      out << "LOOP SUMMARY #" << code.get("index");
      return out;
    }
  }

  return goto_programt::output_instruction(ns, identifier, out, it);
}
