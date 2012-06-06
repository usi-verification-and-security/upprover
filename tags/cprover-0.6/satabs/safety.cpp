/*******************************************************************\

Module: Safety Checking

Author: Daniel Kroening

Date: August 2008

\*******************************************************************/

#include "safety.h"
#include "cegar_loop.h"
#include "status_values.h"

/*******************************************************************\

   Class: safety

 Purpose: Perform Safety Check
 
\*******************************************************************/

class safetyt:public messaget
{
public:
  safetyt(
    message_handlert &_message_handler,
    cegar_loopt &_cegar_loop):
    messaget(_message_handler),
    cegar_loop(_cegar_loop)
  {
  }

  int operator()();

protected:
  cegar_loopt &cegar_loop;
};

/*******************************************************************\

Function: safety

  Inputs:

 Outputs:

 Purpose: Perform Termination Check
 
\*******************************************************************/

int safetyt::operator()()
{
  // just run CEGAR now

  int result;

  switch(result=cegar_loop.go())
  {
  case CEGAR_COUNTEREXAMPLE:
    break;

  case CEGAR_PROPERTY_HOLDS:
  default:;
  }

  return result;
}

/*******************************************************************\

Function: safety

  Inputs:

 Outputs:

 Purpose: Perform Termination Check
 
\*******************************************************************/

int safety(cegar_loopt &cegar_loop)
{
  safetyt safety(cegar_loop.get_message_handler(), cegar_loop);
  return safety();
}
