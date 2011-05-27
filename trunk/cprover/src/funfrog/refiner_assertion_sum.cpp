/*******************************************************************

 Module: Refining schema for function summarization.
         Supposed to have different implementations.

 Author: Grigory Fedyukovich

\*******************************************************************/


#include <stdlib.h>
#include "refiner_assertion_sum.h"

/*******************************************************************

 Function: refiner_assertion_sumt::refine

 Inputs:

 Outputs:

 Purpose: Analyses the results of slicing in order to refine,
          Which function call to inline, which to summarize and which to havoc

\*******************************************************************/

void refiner_assertion_sumt::refine()
{
  std::map<irep_idt, std::vector<bool> > func = equation.get_functions();

  switch (mode){
    case FORCE_INLINING:
      reset_inline(summary_info);
      break;
    case RANDOM_SUBSTITUTION:
      reset_random(summary_info, func);
      break;
    case SLICING_RESULT:
      // TODO: strengthen the analysis. for the moment, refinement loop in this mode may not terminate
      reset_depend(summary_info, func);
      break;
    default:
      assert(false);
      break;
  }

  if (havoc_unimportant){
    reset_havoc(summary_info, func);
  }
}

void refiner_assertion_sumt::reset_inline(summary_infot &_summary_info)
{
  std::map<goto_programt::const_targett, call_summaryt>& call_sites = _summary_info.get_call_sites();
  for(std::map<goto_programt::const_targett, call_summaryt>::iterator it=
        call_sites.begin(); it!=call_sites.end(); it++)
  {
    call_summaryt &call_summary = it->second;
    call_summary.set_inline();
    reset_inline(call_summary.get_summary_info());
  }
}

void refiner_assertion_sumt::reset_random(summary_infot &_summary_info, std::map<irep_idt, std::vector<bool> > functions)
{
  std::map<goto_programt::const_targett, call_summaryt>& call_sites = _summary_info.get_call_sites();
  for(std::map<goto_programt::const_targett, call_summaryt>::iterator it=
        call_sites.begin(); it!=call_sites.end(); it++)
  {
    call_summaryt &call_summary = it->second;
    summary_infot &_summary_info = call_summary.get_summary_info();
    if (!call_summary.is_in_call_stack()){;
      if (is_summary(functions, _summary_info.get_function_id(), false)){
        if (rand() % 1000 < 300 || rand() % 1000 > 800){
          call_summary.set_inline();
        }
      }
    }
    reset_random(_summary_info, functions);
  }
}

void refiner_assertion_sumt::reset_depend(summary_infot &_summary_info, std::map<irep_idt, std::vector<bool> > functions)
{
  std::map<goto_programt::const_targett, call_summaryt>& call_sites = _summary_info.get_call_sites();
  for(std::map<goto_programt::const_targett, call_summaryt>::iterator it=
        call_sites.begin(); it!=call_sites.end(); it++)
  {
    call_summaryt &call_summary = it->second;
    summary_infot &_summary_info = call_summary.get_summary_info();

    if (!call_summary.is_in_call_stack()){
      if (!any_applicable(functions, _summary_info.get_function_id(), false)){
        call_summary.set_inline();
      }
    }
    reset_depend(_summary_info, functions);
  }
}

void refiner_assertion_sumt::reset_havoc(summary_infot &_summary_info, std::map<irep_idt, std::vector<bool> > functions)
{
  std::map<goto_programt::const_targett, call_summaryt>& call_sites = _summary_info.get_call_sites();
  for(std::map<goto_programt::const_targett, call_summaryt>::iterator it=
        call_sites.begin(); it!=call_sites.end(); it++)
  {
    call_summaryt &call_summary = it->second;
    summary_infot &_summary_info = call_summary.get_summary_info();
    if (!call_summary.is_in_call_stack()){
      if (!is_summary(functions, _summary_info.get_function_id(), true)){
        call_summary.set_nondet();
      }
    }
    reset_havoc(_summary_info, functions);
  }
}

bool is_summary(std::map<irep_idt, std::vector<bool> > mapt, irep_idt fun, bool def)
{
  return sum_prop(mapt, fun, 0, def);
}

bool any_applicable(std::map<irep_idt, std::vector<bool> > mapt, irep_idt fun, bool def)
{
  return sum_prop(mapt, fun, 1, def);
}

bool is_ignored(std::map<irep_idt, std::vector<bool> > mapt, irep_idt fun, bool def)
{
  return sum_prop(mapt, fun, 2, def);
}

bool sum_prop(std::map<irep_idt, std::vector<bool> > mapt, irep_idt fun, unsigned pos, bool def)
{
  if (mapt.count(fun) == 0)
  {
    return def;
  }
  std::vector<bool> props = mapt.find(fun)->second;
  if (props.size() <= pos){
    return def;
  }
  return props.at(pos);
}
