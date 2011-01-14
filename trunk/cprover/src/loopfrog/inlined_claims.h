/*******************************************************************

 Module: Inlined Claims Handling

 Author: CM Wintersteiger

 \*******************************************************************/

#ifndef _CPROVER_LOOPFROG_INLINED_CLAIMS_H_
#define _CPROVER_LOOPFROG_INLINED_CLAIMS_H_

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>

#include "loopstore.h"
#include "call_stack.h"
#include "check_claims.h"

class show_inlined_claimst
{
protected:
  const goto_functionst &functions;
  const loopstoret &imprecise_loops;
  const loopstoret &precise_loops;
  const namespacet &ns;
    
  call_stackt call_stack;
  
public:
  unsigned claim_count;
  
  show_inlined_claimst(
    const goto_functionst &_functions,
    const loopstoret &_imprecise_loops,
    const loopstoret &_precise_loops,
    const namespacet &_ns) :
      functions(_functions),
      imprecise_loops(_imprecise_loops),
      precise_loops(_precise_loops),
      ns(_ns),
      claim_count(0) {}
    
  void show(const goto_programt &program, std::ostream &out);
  
  void show_claim(
    goto_programt::const_targett &it,
    const call_stackt &call_stack,
    unsigned claim_nr,
    std::ostream &out) const;
};

void show_inlined_claims(
  const goto_programt &program, 
  const goto_functionst &functions,
  const loopstoret &imprecise_loops,
  const loopstoret &precise_loops,
  const namespacet &ns,
  std::ostream &out);

unsigned count_inlined_claims(
  const goto_programt &program, 
  const goto_functionst &functions,
  const loopstoret &imprecise_loops,
  const loopstoret &precise_loops);

unsigned find_marked_claim(
  const goto_functionst &functions,
  const loopstoret &precise_loops,
  const irep_idt &mark,
  const claim_numberst &claim_numbers);

#endif /*_CPROVER_LOOPFROG_INLINED_CLAIMS_H_*/
