/*******************************************************************\

Module: Loop Summaries 

Author: CM Wintersteiger
        Aliaksei Tsitovich

\*******************************************************************/

#ifndef _LOOPFROG_SUMMARY_H_
#define _LOOPFROG_SUMMARY_H_

#include <set>
#include <expr.h>

#include <goto-programs/goto_program.h>
#include <pointer-analysis/value_sets.h>

typedef enum { DOES_NOT_TERMINATE, TERMINATES_WITH_ASSUMPTION, TERMINATES } termination_typet;

typedef std::map<exprt, exprt> var_mappingt;

struct transition_invariantt
{
  exprt invariant;
  var_mappingt mapping;
  std::set<exprt> assumptions;
  transition_invariantt( const exprt& e, const var_mappingt & m, const std::set<exprt> & a ) :
    invariant( e ), mapping( m ), assumptions( a ) {};
  transition_invariantt( const exprt& e, const var_mappingt & m) :
    invariant( e ), mapping( m ){};
  transition_invariantt( const exprt& e, const var_mappingt & m, const exprt & a) :
    invariant( e ), mapping( m ){assumptions.insert(a);};
};

typedef std::list<transition_invariantt> transition_invariantst;

struct loop_summaryt
{
public:
  std::set<exprt> variant;
  std::set<exprt> invariants;
  std::set<exprt> rhs_expressions;

  transition_invariantst transition_invariants;
  termination_typet termination_type;

  goto_programt::const_targett loop_head;

  void get_variants_program(
    value_setst &value_sets,
    goto_programt &goto_program);
  
  void get_preconditions_program(
    contextt &context, 
    goto_programt &goto_program);
  
  void get_invariants_program(
    contextt &context, 
    goto_programt&);

  loop_summaryt():termination_type(DOES_NOT_TERMINATE){}

protected:
  void assign_nondet_rec(
    const exprt &e,
    value_setst &value_sets,
    goto_programt &program) const;
};

#endif 
