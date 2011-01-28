/*******************************************************************

 Module: Summarizing information associated with a single function,
 i.e., a set of discovered summaries and set of call sites.

 Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_FUNCTION_INFO_H
#define CPROVER_FUNCTION_INFO_H

#include <irep.h>
#include <expr.h>
#include <hash_cont.h>

// Collected summarization info for a single function
class function_infot {
public:
  function_infot(const irep_idt& _function) : function(_function) {}

private:
  // Id of the function
  irep_idt function;
  // The collected summaries
  // TODO: We will need some mapping of parameters...
  std::vector<exprt> summaries;
};

typedef hash_map_cont<irep_idt, function_infot> function_infost;

#endif
