/*******************************************************************

 Module: Summarizing information associated with a single function,
 i.e., a set of discovered summaries and set of call sites.

 Author: Ondrej Sery

\*******************************************************************/

#ifndef FUNCTION_INFO_H_
#define FUNCTION_INFO_H_

#include <irep.h>
#include <expr.h>

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

#endif /*FUNCTION_INFO_H_*/

