  /*******************************************************************\

 Module: A string zero-termination invariant

 Author: CM Wintersteiger

\*******************************************************************/

#ifndef __CPROVER_LOOPFOG_INVARIANTS_INVARIANT_TEST_H_
#define __CPROVER_LOOPFOG_INVARIANTS_INVARIANT_TEST_H_

#include <set>
#include <string>

#include <expr.h>
#include <std_expr.h>
#include <context.h>

#include "../summary.h"

typedef enum { STATE, TRANSITION, STATE_AND_TRANSITION } invariant_test_typet;

class invariant_testt
{
protected:
  contextt &context;
  unsigned temporary_counter;

public:
  const irep_idt short_name;
  const irep_idt long_name;
  invariant_test_typet test_type;

  invariant_testt(
    const std::string &sn,
    const std::string &ln,
    contextt &_context,
    invariant_test_typet inv_type = STATE) :
      context(_context),
      temporary_counter(0),
      short_name(sn),
      long_name(ln),
      test_type(inv_type) {}

  virtual ~invariant_testt(void) {}

  virtual void get_invariants(
    const loop_summaryt &summary,
    std::set<exprt> &potential_invariants) { };

  virtual void get_transition_invariants(
      const loop_summaryt &summary,
      transition_invariantst &candidates) { };

protected:
  symbol_exprt get_temporary_symbol(const typet &type);
};

#endif /*__CPROVER_LOOPFOG_INVARIANTS_INVARIANT_TEST_H_*/
