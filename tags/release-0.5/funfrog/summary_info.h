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
typedef enum {HAVOC, SUMMARY, INLINE} summary_precisiont;

// Forward def.
class call_summaryt;

// Summary information for a body of a function
class summary_infot {
public:

  summary_infot(summary_infot *_parent) : function_id(ID_nil), parent(_parent) {}

  void clear() { call_sites.clear(); }

  void initialize(const summarization_contextt &summarization_context,
      const goto_programt &code, size_t stack_depth = 0);

  void set_function_id(const irep_idt& _function_id) { function_id = _function_id; }

  std::map<goto_programt::const_targett, call_summaryt>& get_call_sites() { return call_sites; }

  const irep_idt& get_function_id() const { return function_id; }

  void set_initial_precision(
      const summarization_contextt& summarization_context,
      const assertion_infot& assertion, unsigned i);
  
  bool is_root() { return parent == NULL; }
  
  summary_infot& get_parent() { return *parent; }

  static void process_goto_locations();

  static void setup_default_precision(init_modet init);

  static std::vector<call_summaryt*>& get_call_summaries() { return functions; }

  static unsigned get_summaries_count(){ return get_precision_count(SUMMARY); }

  static unsigned get_nondets_count(){ return get_precision_count(HAVOC); }

private:
  std::map<goto_programt::const_targett, call_summaryt> call_sites;
  irep_idt function_id;
  summary_infot *parent;

  static std::vector<call_summaryt*> functions;
  static std::vector<std::pair<unsigned, unsigned> > goto_ranges;
  static std::map<goto_programt::const_targett, std::vector<unsigned> > assertion_locs;
  static summary_precisiont default_precision;
  static unsigned global_loc;

  static unsigned get_precision_count(summary_precisiont precision);
};

// Summary information for a specific call site
class call_summaryt {
public:
  call_summaryt(summary_infot *_parent, size_t _stack_depth, unsigned _call_location) :
     precision(HAVOC),
     summary_info(_parent),
     stack_depth(_stack_depth),
     call_location(_call_location),
     call_stack(0)
  {}

  void set_inline() { precision = INLINE; }
  void set_summary() { precision = SUMMARY; }
  void set_nondet() { precision = HAVOC; }

  bool is_in_call_stack() { return call_stack; }

  summary_precisiont get_precision() { return precision; }

  summary_infot& get_summary_info() { return summary_info; }

private:
  summary_precisiont precision;
  summary_infot summary_info;
  size_t stack_depth;
  unsigned call_location;
  bool call_stack;

  void initialize(const summarization_contextt &summarization_context,
          const irep_idt &target_function, size_t stack_depth);

  friend class summary_infot;
};

#endif
