/*******************************************************************

 Module: Keeps current state of the assertion checking in progress,
 i.e., to each function call it assigns a level of summarization 
 used in the symex analysis.

 Author: Ondrej Sery

\*******************************************************************/

#ifndef SUMMARY_INFO_H_
#define SUMMARY_INFO_H_

#include <map>
#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>

#include <loopfrog/loopstore.h>

#include "assertion_info.h"
#include "summarization_context.h"

// Forward def.
class call_summaryt;

// Summary information for a body of a function
class summary_infot {
public:
  summary_infot() {}

  void clear() { call_sites.clear(); }
  void initialize(const summarization_contextt& summarization_context,
      const goto_programt& code,
      const assertion_infot& assertion, size_t stack_depth = 0);
  const std::map<goto_programt::const_targett,call_summaryt>& get_call_sites() { return call_sites; }

private:
  std::map<goto_programt::const_targett,call_summaryt> call_sites;
  irep_idt function;
};

// Type of summarization applied at a specific call-site
typedef enum {NONDET, SUMMARY, INLINE} summary_precisiont;

// Summary information for a specific call site
class call_summaryt {
public:
  call_summaryt() : precision(NONDET) {}

  void set_inline(const summarization_contextt&);
  void set_summary() { precision = SUMMARY; }
  void set_nondet() { precision = NONDET; }
  summary_precisiont get_precision() const { return precision; }

private:
  summary_precisiont precision;
  summary_infot summary_info;

  void set_inline(const summarization_contextt &summarization_context,
    const irep_idt &target_function, const assertion_infot &assertion,
    size_t stack_depth);

  friend class summary_infot;
};

#endif /*SUMMARY_INFO_H_*/

