/*******************************************************************\

Module: Generic Loop Summarization

Author: CM Wintersteiger

\*******************************************************************/

#ifndef _LOOPFROG_SUMMARIZATION_H_
#define _LOOPFROG_SUMMARIZATION_H_

#include <list>
#include <map>

#include <cmdline.h>
#include <time_stopping.h>
#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>
#include <goto-symex/symex_target_equation.h>

#include "invariants/invariant_test.h"

#include <termination/replace_identifier.h>

#include "value_set_duplication_adaptor.h"
#include "summary.h"
#include "loopstore.h"
#include "symex_assertion.h"

class summarizationt
{
protected:
  namespacet ns;
  contextt &context;
  const goto_functionst &goto_functions;
  const loopstoret &imprecise_loops;
  const loopstoret &precise_loops;
  value_setst &value_sets;
  const std::string &stats_dir;
  goto_programt::const_targett original_loop_head;

  class invariant_statt {
  public:
    unsigned passed;
    unsigned failed;
    irep_idt long_name;
    fine_timet time;

    invariant_statt(void) : passed(0), failed(0), long_name(""), time(0) {}
  };

  typedef std::map<irep_idt, invariant_statt > invariant_statst;

public:
  unsigned seen_loops;
  invariant_statst invariant_stats;
  typedef std::list<invariant_testt*> invariant_testst;
  invariant_testst invariant_tests;
  invariant_testst transition_invariant_tests;

  unsigned long max_mem_used;
  const optionst &options;

  summarizationt(
    contextt &_context,
    const goto_functionst &_goto_functions,
    const loopstoret &_imprecise_loops,
    const loopstoret &_precise_loops,
    value_setst &_value_sets,
    const std::string &_stats_dir,
    const optionst &_opts) :
      ns(_context),
      context(_context),
      goto_functions(_goto_functions),
      imprecise_loops(_imprecise_loops),
      precise_loops(_precise_loops),
      value_sets(_value_sets),
      stats_dir(_stats_dir),
      seen_loops(0),
      max_mem_used(0),
      options(_opts) {};

  virtual ~summarizationt( void );

  virtual void summarize_loop(
    goto_programt::const_targett &original_head,
    goto_programt &source,
    loop_summaryt &summary);

  void run_tests(
    goto_programt &source,
    loop_summaryt &summary);

  void run_tests_incremental(
    goto_programt &source,
    loop_summaryt &summary);

  void schedule(invariant_testt* test);

  void print_statistics(
    std::ostream &out) const;

protected:

  void new_loop_number(void) { seen_loops++; }

  void create_program(
    goto_programt &src,
    const exprt &invariant,
    goto_programt &dest) const;

  void prepare_program_with_transition_invariant(
    goto_programt &src,
    const var_mappingt &post_pre_map,
    const exprt &invariant,
    goto_programt &dest) const;

  void get_variant(
    const goto_programt &src,
    loop_summaryt &summary) const;

  void test_invariant(
    goto_programt &source,
    const exprt &invariant,
    const irep_idt &statname,
    loop_summaryt &summary);

  termination_typet test_transition_invariant(
    goto_programt &source,
    const transition_invariantt &candidate,
    const irep_idt &statname,
    loop_summaryt &summary);


  void get_loop_equation(
    contextt &temp_context,
    symex_assertiont &symex,
    goto_programt &source,
    symex_target_equationt &equation,
    std::ofstream &out);

  void get_user_invariants_fromfile(
    std::set<exprt> &user_invariants);

  bool is_compositional( const exprt &disjunction);

  void get_pre_post(
    const std::set<exprt> &symbols,
    replace_idt &varmap) const;

};

#endif
