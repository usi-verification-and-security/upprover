/*******************************************************************

 Module: Loopfrog's final claim checking

 Author: CM Wintersteiger

\*******************************************************************/

#ifndef _CPROVER_LOOPFROG_CHECK_CLAIMS_H_
#define _CPROVER_LOOPFROG_CHECK_CLAIMS_H_

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>

class claim_statst
{
public:
  claim_statst(void) :
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
};


typedef std::map<goto_programt::const_targett, 
                std::pair<bool /* checked? */, bool /* safe? */ > > claim_mapt;
typedef std::map<goto_programt::const_targett, unsigned > claim_numberst;


void get_claims(const goto_functionst &goto_functions,
                claim_mapt &claim_map,
                claim_numberst &claim_numbers);

void show_claims(const namespacet &ns,
                 const claim_mapt &claim_map, 
                 const claim_numberst &claim_numbers);

claim_statst check_claims(
  const namespacet &ns,
  goto_programt &leaping_program,
  const goto_functionst &goto_functions,
  const std::string &stats_dir,
  claim_mapt &claim_map,
  claim_numberst &claim_numbers,
  unsigned claim_nr = 0,
  bool show_pass = false,
  bool show_fail = true,
  bool show_progress = true,
  bool save_files=false,
  bool use_smt=false);

#endif /*_CPROVER_LOOPFROG_CHECK_CLAIMS_H_*/
