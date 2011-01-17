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

// Forward def.
class call_summaryt;

// Summary information for a body of a function
class summary_infot {
public:
  summary_infot() {}

  void clear() {call_sites.clear();}

private:
  std::map<goto_programt::const_targett,call_summaryt> call_sites;
  irep_idt function;
};

// Type of summarization applied at a specific call-site
typedef enum {NONDET, SUMMARY, INLINE} summary_precisiont;

// Summary information for a specific call site
class call_summaryt {
  call_summaryt() : precision(NONDET) {}

  void set_inline();
  void set_summary() { precision = SUMMARY; }
  void set_nondet() { precision = NONDET; }
  summary_precisiont get_precision() const { return precision; }
private:
  summary_precisiont precision;
  summary_infot info;
};

#endif /*SUMMARY_INFO_H_*/

