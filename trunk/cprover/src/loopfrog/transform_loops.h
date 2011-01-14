/*******************************************************************

 Module: Loop Transformations

 Author: CM Wintersteiger

\*******************************************************************/

#ifndef _CPROVER_LOOPFROG_TRANSFORM_LOOPS_H_
#define _CPROVER_LOOPFROG_TRANSFORM_LOOPS_H_

#include <util/message_stream.h>
#include <goto-programs/goto_functions.h>

class loop_transformt : public message_streamt
{
private:
  contextt &context;
  unsigned trans_counter;

public:
  loop_transformt(
    contextt &_context,
    message_handlert &_message_handler) :
      message_streamt(_message_handler),
      context(_context),
      trans_counter(0) {}

  void transform(goto_functionst &goto_functions);
  void transform(goto_programt &goto_program);

  void run_checks(
    const goto_programt &goto_program,
    goto_programt::const_targett begin,
    goto_programt::const_targett end);

  void output_loop(
    std::ostream &out,
    const goto_programt &goto_program,
    goto_programt::const_targett begin,
    goto_programt::const_targett end);

  void transform_do_while(
    goto_programt &program,
    goto_programt::targett &begin,
    goto_programt::targett &end) const;

  void split_multi_head(
    goto_programt &program,
    goto_programt::targett begin,
    goto_programt::targett end);

  void move_returns(
    goto_programt &program,
    goto_programt::targett begin,
    goto_programt::targett end);


  bool check_loop_interleaved(
    const goto_programt &program,
    goto_programt::const_targett begin,
    goto_programt::const_targett end);

  bool check_loop_exits(
    const goto_programt &program,
    goto_programt::const_targett begin,
    goto_programt::const_targett end);

  bool check_loop_entries(
    const goto_programt &program,
    goto_programt::const_targett begin,
    goto_programt::const_targett end);


  bool is_exit(
    const goto_programt::targett &loc,
    const goto_programt::targett &begin,
    const goto_programt::targett &end) const;

  bool is_far_exit(
    const goto_programt::targett &loc,
    const goto_programt::targett &begin,
    const goto_programt::targett &end) const;

  bool is_forward_exit(
    const goto_programt::targett &loc,
    const goto_programt::targett &begin,
    const goto_programt::targett &end) const;

  bool is_backward_exit(
    const goto_programt::targett &loc,
    const goto_programt::targett &begin,
    const goto_programt::targett &end) const;

  bool is_forward_entry(
    const goto_programt::targett &loc,
    const goto_programt::targett &begin,
    const goto_programt::targett &end) const;

  bool is_early_entry(
    const goto_programt::targett &loc,
    const goto_programt::targett &begin,
    const goto_programt::targett &end) const;

  bool is_backward_entry(
    const goto_programt::targett &loc,
    const goto_programt::targett &begin,
    const goto_programt::targett &end) const;

  bool is_in_loop(
    const goto_programt::targett &loc,
    const goto_programt::targett &begin,
    const goto_programt::targett &end) const;

  void recheck_exits(
    const goto_programt::targett &begin,
    const goto_programt::targett &end,
    std::set<goto_programt::targett> &exits) const;

  void analyze(
    goto_programt &program,
    goto_programt::targett &begin,
    goto_programt::targett &end,
    std::set<goto_programt::targett> &entries,
    std::set<goto_programt::targett> &exits);

  void transform(
    goto_programt &program,
    goto_programt::targett &begin,
    goto_programt::targett &end,
    std::set<goto_programt::targett> &entries,
    std::set<goto_programt::targett> &exits);

  void transform_entries(
    goto_programt &program,
    goto_programt::targett &begin,
    goto_programt::targett &end,
    const exprt &loop_symbol,
    std::set<goto_programt::targett> &entries);

  void transform_exits(
    goto_programt &program,
    goto_programt::targett &begin,
    goto_programt::targett &end,
    const exprt &loop_symbol,
    std::set<goto_programt::targett> &exits);

  exprt get_new_variable(void);
};

void transform_loops(goto_functionst &goto_functions,
                     contextt &context,
                     message_handlert &message_handler);

void transform_loops(goto_programt &goto_program,
                     contextt &context,
                     message_handlert &message_handler);

#endif /*_CPROVER_LOOPFROG_TRANSFORM_LOOPS_H_*/
