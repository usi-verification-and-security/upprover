/*******************************************************************\

Module: Loop Summarization (without Inlining)

Author: CM Wintersteiger

\*******************************************************************/

#ifndef _LOOPFROG_LOOP_SUMMARIZER_NI_H_
#define _LOOPFROG_LOOP_SUMMARIZER_NI_H_

#include <map>

#include <message_stream.h>
#include <irep.h>

#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_program.h>

#include "summarization.h"
#include "summary.h"
#include "loopstore.h"

class loop_summarizer_statst
{
public:
  unsigned good;
  unsigned good_checked;
  unsigned bad;
  unsigned bad_checked;

  loop_summarizer_statst(void) :
    good(0),
    good_checked(0),
    bad(0),
    bad_checked(0) {};
};

class loop_summarizert : public message_streamt
{
private:
  const namespacet ns;
  contextt &context;
  summarizationt &summarization;
  goto_functionst &goto_functions;
  const cmdlinet &cmdline;

  typedef hash_map_cont<irep_idt, unsigned, irep_id_hash> function_call_statst;
  function_call_statst function_call_stats;

  typedef hash_map_cont<irep_idt, std::set<irep_idt>, irep_id_hash> f_localst;
  f_localst f_locals;

  typedef hash_set_cont<irep_idt, irep_id_hash> functions_summarizedt;
  functions_summarizedt functions_summarized;

  typedef hash_set_cont<irep_idt, irep_id_hash> recursion_sett;
  recursion_sett recursion_set;

  unsigned current_loop_nr;
  unsigned total_loops;

public:
  typedef hash_map_cont<irep_idt, unsigned, irep_id_hash> predischarget;
  predischarget predischarge_pass;
  predischarget predischarge_fail;

  loopstoret &imprecise_loops;
  loopstoret &precise_loops;
  value_setst &value_sets;
  const std::string &stats_dir;

public:
  loop_summarizert(
    contextt &_context,
    summarizationt &_summarization,
    goto_functionst &_goto_functions,
    loopstoret &_imprecise_loops,
    loopstoret &_precise_loops,
    value_setst &_value_sets,
    const std::string &_stats_dir,
    message_handlert &_message_handler,
    const cmdlinet &_cmdline) :
      message_streamt(_message_handler),
      ns(_context),
      context(_context),
      summarization(_summarization),
      goto_functions(_goto_functions),
      cmdline(_cmdline),
      current_loop_nr(0),
      total_loops(0),
      imprecise_loops(_imprecise_loops),
      precise_loops(_precise_loops),
      value_sets(_value_sets),
      stats_dir(_stats_dir),
      return_value_counter(0),
      locals_counter(0) {}

  void summarize(
    const irep_idt &name,
    goto_programt &program,
    goto_functionst &goto_functions);

protected:
  unsigned return_value_counter;
  unsigned locals_counter;

  void summarize_rec(
      const irep_idt &name,
      goto_programt &program);

  void summarize_loop(
    goto_programt &source,
    goto_programt::targett begin,
    goto_programt::targett end);

  void move_returns(goto_programt &dest);

  unsigned fix_location_numbering(goto_programt &program) const;
  unsigned fix_location_numbering(goto_functionst &functions) const;

  void create_imprecise_loop_summary(
    loop_summaryt &summary) const;

  void create_precise_loop_summary(
    goto_programt &loop_program,
    loop_summaryt &summary);

  void prepare_loop_body(goto_programt &source);
};

loop_summarizer_statst summarize(
  goto_functionst &goto_functions,
  contextt &context,
  summarizationt& summarization,
  loopstoret &_imprecise_loops,
  loopstoret &_precise_loops,
  value_setst &_value_sets,
  message_handlert &message_handler,
  cmdlinet &cmdline,
  const std::string &stats_dir);

#endif
