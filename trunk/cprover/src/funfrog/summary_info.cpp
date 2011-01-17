/*******************************************************************

 Module: Keeps current state of the assertion checking in progress,
 i.e., to each function call it assigns a level of summarization 
 used in the symex analysis.

 Author: Ondrej Sery

\*******************************************************************/

#include "summary_info.h"

void
call_summaryt::set_inline()
{
  precision = INLINE;
  // TODO:fill summary_info with call_sites
}
