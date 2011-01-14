/*******************************************************************

 Module: Loopfrog's final claim checking

 Author: CM Wintersteiger

\*******************************************************************/

#ifndef _CPROVER_LOOPFROG_CHECK_CLAIMS_H_
#define _CPROVER_LOOPFROG_CHECK_CLAIMS_H_

#include <goto-programs/goto_program.h>
#include "invariant_propagation_adaptor.h"

#include "loopstore.h"

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
                const loopstoret &precise_loops,
                claim_mapt &claim_map,
                claim_numberst &claim_numbers);

void show_claims(const namespacet &ns,
                 const claim_mapt &claim_map, 
                 const claim_numberst &claim_numbers);

claim_statst check_claims(
  const namespacet &ns,
  goto_programt &leaping_program,
  const goto_functionst &goto_functions,
  const loopstoret &imprecise_loops,
  const loopstoret &precise_loops,
  const std::string &stats_dir,
  claim_mapt &claim_map,
  claim_numberst &claim_numbers,
  unsigned claim_nr = 0,
  bool show_pass = false,
  bool show_fail = true,
  bool show_progress = true,
  bool save_files=false,
  bool assume_guarantee=false,
  bool check_by_invariant=false,
  bool use_smt=false);

claim_statst check_claims_using_domain(
  const namespacet &ns,
  goto_functionst &goto_functions,
  const invariant_propagation_adaptort &invariant_propagation,
  bool simplify_claims = false);

#endif /*_CPROVER_LOOPFROG_CHECK_CLAIMS_H_*/
