/*******************************************************************\

Module: Symex target equation which tracks different partitions for
different deferred functions.

Author: Ondrej Sery

\*******************************************************************/

#include "partitioning_target_equation.h"

/*******************************************************************\

Function: partitioning_target_equationt::convert

  Inputs:

 Outputs:

 Purpose: Convert all the SSA steps into the corresponding formulas in
 the corresoponding partitions

\*******************************************************************/
void partitioning_target_equationt::convert(
  prop_convt &prop_conv)
{
  convert_guards(prop_conv);
  convert_assignments(prop_conv);
  convert_assumptions(prop_conv);
  convert_assertions(prop_conv);
  convert_io(prop_conv);
}
