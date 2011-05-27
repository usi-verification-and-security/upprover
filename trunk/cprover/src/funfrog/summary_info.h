/*******************************************************************

 Module: Keeps current state of the assertion checking in progress,
 i.e., to each function call it assigns a level of summarization 
 used in the symex analysis.

 Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_SUMMARY_INFO_H
#define CPROVER_SUMMARY_INFO_H

#include <map>
#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>

#include <loopfrog/loopstore.h>

#include "assertion_info.h"
#include "summarization_context.h"

// Type of summarization applied at a specific call-site
typedef enum {NONDET, SUMMARY, INLINE} summary_precisiont;

// Forward def.
class call_summaryt;

// Summary information for a body of a function
class summary_infot {
public:

  summary_infot() : function_id(ID_nil) {}

  void clear() { call_sites.clear(); }

  void initialize(const summarization_contextt &summarization_context,
      const goto_programt &code, const assertion_infot &assertion,
      size_t stack_depth = 0);

  void set_function_id(const irep_idt& _function_id) { function_id = _function_id; }

  std::map<goto_programt::const_targett,call_summaryt>& get_call_sites() { return call_sites; }

  const irep_idt& get_function_id() const { return function_id; }

  void set_default_precision(init_modet init);

private:
  std::map<goto_programt::const_targett, call_summaryt> call_sites;
  irep_idt function_id;
  static summary_precisiont default_precision;
};

// Summary information for a specific call site
class call_summaryt {
public:
  call_summaryt() : precision(NONDET) {}

  void set_inline() { precision = INLINE; }
  void set_summary() { precision = SUMMARY; }
  void set_nondet() { precision = NONDET; }

  bool is_in_call_stack() { return call_stack; }

  summary_precisiont get_precision() { return precision; }

  summary_infot& get_summary_info() { return summary_info; }

private:
  summary_precisiont precision;
  summary_infot summary_info;
  bool call_stack;

  void initialize(const irep_idt &target_function)
    { summary_info.set_function_id(target_function);}
  void set_precision_deep(
          summary_precisiont _precision,
          const summarization_contextt &summarization_context,
          const irep_idt &target_function,
          const assertion_infot &assertion,
          size_t stack_depth,
          bool _call_stack = false);

  friend class summary_infot;
};

#endif
