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

#include "assertion_info.h"
#include "summarization_context.h"

// Type of summarization applied at a specific call-site
typedef enum {HAVOC, SUMMARY, INLINE} summary_precisiont;

// Forward def.
class call_summaryt;
typedef std::map<goto_programt::const_targett, call_summaryt> call_sitest;
typedef std::map<goto_programt::const_targett, unsigned> location_mapt;
typedef std::set<goto_programt::const_targett> locationst;

// Summary information for a body of a function
class summary_infot {
public:

  summary_infot(summary_infot *_parent)
          : function_id(ID_nil), parent(_parent), assertion_in_subtree(false) { }

  void clear() { call_sites.clear(); }

  void set_function_id(const irep_idt& _function_id) { function_id = _function_id; }

  call_sitest& get_call_sites() { return call_sites; }

  const summary_ids_sett& get_used_summaries() const { return used_summaries; }
  void set_used_summaries(summary_ids_sett& other)  { 
    used_summaries.swap(other); 
  }
  void add_used_summary(summary_idt id) { used_summaries.insert(id); }
  void clear_used_summaries() { used_summaries.clear(); }

  const irep_idt& get_function_id() const { return function_id; }

  void set_initial_precision(
      const summary_precisiont default_precision,
      //location_mapt& assertions,
      const summarization_contextt& summarization_context,
      const assertion_infot& assertion, bool assert_grouping);

  bool is_root() const { return parent == NULL; }
  bool has_assertion_in_subtree() const { return assertion_in_subtree; }
  bool is_assertion_enabled(const goto_programt::const_targett& assertion) const {
    return enabled_assertions.find(assertion) != enabled_assertions.end();
  }

  summary_infot& get_parent() { return *parent; }
  location_mapt& get_assertions() { return assertions; };

private:
  call_sitest call_sites;
  location_mapt assertions;
  locationst enabled_assertions;
  irep_idt function_id;
  summary_infot *parent;
  summary_ids_sett used_summaries;
  bool assertion_in_subtree;
  
  void set_initial_precision(
        summary_precisiont default_precision,
        //location_mapt& assertions,
        const summarization_contextt& summarization_context,
        const assertion_infot& assertion, unsigned last_assertion_loc);
  
  bool mark_enabled_assertions(
        //location_mapt& assertions,
        const summarization_contextt& summarization_context,
        const assertion_infot& assertion, unsigned depth, 
        bool parent_stack_matches, bool assert_grouping,
        unsigned& last_assertion_loc);
};

// Summary information for a specific call site
class call_summaryt {
public:
  call_summaryt(summary_infot *_parent, unsigned _call_location) :
     precision(HAVOC),
     summary_info(_parent),
     call_location(_call_location)
  {}

  void set_inline() { precision = INLINE; }
  void set_summary() { precision = SUMMARY; }
  void set_nondet() { precision = HAVOC; }
  void set_call_location(unsigned loc) { call_location = loc; }

  summary_precisiont get_precision() const { return precision; }
  summary_infot& get_summary_info() { return summary_info; }
  unsigned get_call_location() { return call_location; }

private:
  summary_precisiont precision;
  summary_infot summary_info;
  unsigned call_location;

  friend class summary_infot;
};

#endif
