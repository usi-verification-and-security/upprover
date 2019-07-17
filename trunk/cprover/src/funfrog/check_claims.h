/*******************************************************************

 Module: Inspired by Loopfrog's final claim checking

\*******************************************************************/

#ifndef _CPROVER_LOOPFROG_CHECK_CLAIMS_H_
#define _CPROVER_LOOPFROG_CHECK_CLAIMS_H_

#include <cstdlib>
#include <util/options.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>
#include <util/ui_message.h>
#include "unwind.h"
#include "call_stack.h"

class claim_statst:public messaget, public unwindt
{

public:
  claim_statst(unsigned int max_unwind) : unwindt(max_unwind),
    total_claims(0),
    claims_passed(0),
    claims_failed(0),
    max_mem_used(0),
    max_instruction_count(0) {}

  unsigned total_claims;
  unsigned claims_passed;
  unsigned claims_failed;

  unsigned long max_mem_used;
  unsigned long max_instruction_count;

  claim_statst &operator+(const claim_statst &other)
  {
    total_claims += other.total_claims;
    claims_passed += other.claims_passed;
    claims_failed += other.claims_failed;

    return *this;
  }

  goto_programt::const_targett find_assertion(
    const goto_programt::const_targett &start,
    const goto_functionst &goto_functions,
    call_stackt &stack);

};


typedef std::map<goto_programt::const_targett, 
                std::pair<bool /* checked? */, bool /* safe? */ > > claim_checkmapt;
typedef std::map<goto_programt::const_targett, unsigned > claim_numberst;


void get_claims(const goto_functionst &goto_functions,
                claim_checkmapt &claim_checkmap,
                claim_numberst &claim_numbers);

void store_claims(const claim_checkmapt &claim_checkmap,
    const claim_numberst &claim_numbers);

void check_claims(
        const goto_modelt & goto_model,
        claim_checkmapt & claim_checkmap,
        claim_numberst & claim_numbers,
        optionst & options,
        ui_message_handlert & _message_handler,
        unsigned claim_user_nr = 0);

#endif /*_CPROVER_LOOPFROG_CHECK_CLAIMS_H_*/
