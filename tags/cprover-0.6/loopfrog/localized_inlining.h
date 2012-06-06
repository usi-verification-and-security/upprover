/*******************************************************************

 Module: Localized Inlining (Assertion dependent precision)

 Author: CM Wintersteiger

\*******************************************************************/

#ifndef _CPROVER_LOOPFROG_LOCALIZED_INLINING_H_
#define _CPROVER_LOOPFROG_LOCALIZED_INLINING_H_

#include <map>
#include <stack>
#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>
#include <message_stream.h>

#include "loopstore.h"
#include "call_stack.h"

goto_programt::const_targett find_assertion(
  const goto_programt::const_targett &start,
  const goto_functionst &goto_functions,
  const loopstoret &imprecise_loops,
  const loopstoret &precise_loops,
  call_stackt &stack);

goto_programt::const_targett find_assertion_n(
  const goto_programt::const_targett &start,
  const goto_functionst &goto_functions,
  const loopstoret &imprecise_loops,
  const loopstoret &precise_loops,
  unsigned n);

goto_programt::const_targett find_assertion_n(
  const goto_programt::const_targett &start,
  const goto_functionst &goto_functions,
  const loopstoret &imprecise_loops,
  const loopstoret &precise_loops,
  call_stackt &call_stack,
  unsigned n);

class goto_inline_localizedt
{
private:
  unsigned total_renamings;

  class inlining_contextt {
  public:
    const goto_programt *goto_program; // the program we're inlining
    exprt return_lhs; // the current return-variable
    unsigned renaming_index; // variable renaming index
    irept function; // the current name of the function/loop
    goto_programt::const_targett end_of_function; // an end-pointer for returns
    bool is_param_context;
  };

public:
    typedef std::map<goto_programt::const_targett,
                     goto_programt::targett> targets_mappingt;
    typedef std::list<goto_programt::targett> unresolved_gotost;
    typedef std::list<goto_programt> temporary_programst;
    typedef std::stack<inlining_contextt> progress_stackt;
    typedef std::set<irep_idt> recursion_sett;
    typedef std::map<goto_programt::targett, goto_programt::targetst>
                                                         disabled_goto_targetst;

  class progresst
  {
  public:
    progresst(
      const goto_programt &_source_program,
      goto_programt &_dest_program,
      bool _keep_assertions=false) :
        source_program(_source_program),
        dest_program(_dest_program),
        keep_assertions(_keep_assertions) {}

    const goto_programt &source_program;
    goto_programt &dest_program;

    targets_mappingt targets_mapping;
    unresolved_gotost unresolved_gotos;
    temporary_programst temporary_programs;
    progress_stackt stack;
    recursion_sett recursion_set;
    goto_programt::const_targett restart_target;
    call_stackt call_stack;
    bool keep_assertions;
    disabled_goto_targetst disabled_goto_targets;
  };

  goto_inline_localizedt(
    const goto_functionst &_goto_functions,
    progresst &_progress,
    const loopstoret &_imprecise_loops,
    const loopstoret &_precise_loops,
    const namespacet &_ns) :
      total_renamings(0),
      goto_functions(_goto_functions),
      imprecise_loops(_imprecise_loops),
      precise_loops(_precise_loops),
      ns(_ns),
      progress(_progress) {}

    goto_programt::const_targett goto_inline(
      const call_stackt &goal_stack,
      goto_programt::const_targett location,
      std::ostream &out);

protected:
  const goto_functionst &goto_functions;
  const loopstoret &imprecise_loops;
  const loopstoret &precise_loops;
  const namespacet &ns;
  progresst &progress;


  void parameter_assignments(
    const locationt &location,
    const code_typet &code_type,
    const exprt::operandst &arguments,
    goto_programt &dest,
    std::ostream &out);

  void replace_return(
    goto_programt &dest,
    goto_programt::const_targett it,
    goto_programt::const_targett end_of_function,
    const exprt &lhs,
    std::ostream &out);

  goto_programt::const_targett goto_inline_int(
    const call_stackt &goal_stack,
    goto_programt::const_targett location,
    std::ostream &out);

  const goto_functionst::goto_functiont &find_function(
    const code_function_callt &call,
    std::ostream &out);

  goto_programt::targett add_skip(goto_programt &program);

  void remove_temporary_program(const goto_programt *program);

  void resolve_gotos( void );
  void cut_unresolved_gotos( void );

  void enable_goto(goto_programt::targett target);
  void disable_goto(goto_programt::targett target);

  bool check_targets(goto_programt &program) const;

  bool is_prefix_of(
    const call_stackt &left,
    const call_stackt &right);
};

#endif /*_CPROVER_LOOPFROG_LOCALIZED_INLINING_H_*/
