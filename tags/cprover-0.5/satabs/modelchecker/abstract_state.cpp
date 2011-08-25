/*******************************************************************\

Module: Counterexamples

Author: Daniel Kroening

  Date: June 2003

\*******************************************************************/

#include <assert.h>

#include "abstract_state.h"

/*******************************************************************\

Function: abstract_stept::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void abstract_stept::output(std::ostream &out) const
{
  switch(step_type)
  {
  case STATE:
    if(has_pc)
    {
      out << "// " << pc->location << std::endl;

      if(pc->is_goto())
        out << "GOTO          ";
      else if(pc->is_assume())
        out << "ASSUME        ";
      else if(pc->is_assert())
        out << "ASSERT        ";
      else if(pc->is_dead())
        out << "DEAD          ";
      else if(pc->is_other())
        out << "OTHER         ";
      else if(pc->is_assign())
        out << "ASSIGN        ";
      else if(pc->is_location())
        out << "LOCATION      ";
      else if(pc->is_start_thread())
        out << "START_THREAD  ";
      else if(pc->is_end_thread())
        out << "END_THREAD    ";
      else if(pc->is_end_function())
        out << "END_FUNCTION  ";
      else if(pc->is_function_call())
        out << "FUNCTION_CALL ";
      else if(pc->is_return())
        out << "RETURN        ";
      else
        out << "(?)           ";
    }
    else
      out << "// no PC" << std::endl;

    if(pc->is_goto())
      out << "branch_taken=" << branch_taken;

    for(unsigned i=0; i<predicate_values.size(); i++)
    {
      out << " b" << i << "=" << predicate_values[i];
    }
    
    out << std::endl;
    break;
    
  case LOOP_BEGIN:
     out << "===== LOOP [:" << std::endl;
     break;

  case LOOP_END:
     out << "===== LOOP :]" << std::endl;
     break;

  default:
    assert(false);
  }
}

/*******************************************************************\

Function: operator <<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream &operator<<(
  std::ostream &out,
  const abstract_stept &step)
{
  step.output(out);
  return out;
}

