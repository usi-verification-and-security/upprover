/*******************************************************************
 Module: Refining schema for function summarization.
         Supposed to have different implementations.

 Author: Grigory Fedyukovich

 \*******************************************************************/

#ifndef CPROVER_REFINER_ASSERTION_SUM_H
#define CPROVER_REFINER_ASSERTION_SUM_H

#include "assertion_info.h"
#include "summary_info.h"
#include "summarization_context.h"
#include "partitioning_target_equation.h"

class refiner_assertion_sumt
{
public:
  refiner_assertion_sumt(
          summarization_contextt &_summarization_context,
          summary_infot &_summary_info,
          partitioning_target_equationt &_target,
          refinement_modet _mode,
          bool _havoc_unimportant,
          std::ostream &_out
          ) :
          summarization_context(_summarization_context),
          summary_info(_summary_info),
          equation(_target),
          mode(_mode),
          havoc_unimportant(_havoc_unimportant),
          out(_out)
          {};

  void refine();

private:

  // Shared information about the program and summaries to be used during
  // analysis
  summarization_contextt &summarization_context;

  // Which functions should be summarized, abstracted from, and which inlined
  summary_infot &summary_info;

  // Store for the symex result
  partitioning_target_equationt &equation;

  // Mode of refinement
  refinement_modet mode;

  // Try to omit non-important summaries (based on result of interpolation)
  bool havoc_unimportant;

  std::ostream &out;

  void reset_inline(summary_infot &_summary_info);
  void reset_random(summary_infot &_summary_info, std::map<irep_idt, std::vector<bool> > functions);
  void reset_depend(summary_infot &_summary_info, std::map<irep_idt, std::vector<bool> > functions);
  void reset_havoc(summary_infot &_summary_info, std::map<irep_idt, std::vector<bool> > functions);
};

bool is_summary(std::map<irep_idt, std::vector<bool> > mapt, irep_idt fun, bool def);
bool any_applicable(std::map<irep_idt, std::vector<bool> > mapt, irep_idt fun, bool def);
bool is_ignored(std::map<irep_idt, std::vector<bool> > mapt, irep_idt fun, bool def);
bool sum_prop(std::map<irep_idt, std::vector<bool> > mapt, irep_idt fun, unsigned pos, bool def);

#endif
