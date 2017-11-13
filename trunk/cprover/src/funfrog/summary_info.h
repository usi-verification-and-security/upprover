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
#include "summary_store_fwd.h"

class summarization_contextt;
class summary_infot;

// Type of summarization applied at a specific call-site
typedef enum {HAVOC, SUMMARY, INLINE} summary_precisiont;

typedef std::map<goto_programt::const_targett, summary_infot> call_sitest;
typedef std::map<goto_programt::const_targett, unsigned> location_mapt;
typedef std::map<goto_programt::const_targett, std::map<unsigned, bool> > location_visitedt;
typedef std::set<goto_programt::const_targett> locationst;

// Summary information for a body of a function
class summary_infot {
public:

  summary_infot(summary_infot *_parent, unsigned _call_location)
          : function_id(ID_nil), parent(_parent), assertion_in_subtree(false),
            precision(HAVOC), call_location(_call_location),
            preserved_node(false), preserved_edge(false), unwind_exceeded(false), recursion_nondet(false), in_loop(false) { }

  void clear() { call_sites.clear(); }

  void set_function_id(const irep_idt& _function_id) { function_id = _function_id; }

  call_sitest& get_call_sites() { return call_sites; }

  const goto_programt::const_targett* get_target();

  const summary_ids_sett& get_used_summaries() const { return used_summaries; }
  void set_used_summaries(summary_ids_sett& other)  { 
    used_summaries.swap(other); 
  }
  void add_used_summary(summary_idt id) { used_summaries.insert(id); }
  void clear_used_summaries() { used_summaries.clear(); }

  const irep_idt& get_function_id() const { return function_id; }

  void set_initial_precision(
      const summary_precisiont default_precision,
      const unsigned last_assertion_loc,
      const summarization_contextt& summarization_context,
      const assertion_infot& assertion);

  bool mark_enabled_assertions(
        const assertion_infot& assertion, unsigned depth,
        bool parent_stack_matches, const unsigned last_assertion_loc);

  bool is_unwind_exceeded() const {
      return unwind_exceeded;
  }

  void set_unwind_exceeded(bool _unwind_exceeded) {
      unwind_exceeded = _unwind_exceeded;
  }

  bool is_root() const { return parent == NULL; }
  bool has_assertion_in_subtree() const { return assertion_in_subtree; }
  bool is_assertion_enabled(const goto_programt::const_targett& assertion) const {
    return enabled_assertions.find(assertion) != enabled_assertions.end();
  }

  summary_infot& get_parent() { return *parent; }
  location_mapt& get_assertions() { return assertions; };

  void set_inline() { precision = INLINE; }
  void set_summary() { precision = SUMMARY; }
  void set_nondet() { precision = HAVOC; }
  void set_precision(summary_precisiont _precision) { precision = _precision; }
  void set_call_location(unsigned loc) { call_location = loc; }
  void set_assertion_in_subtree() { assertion_in_subtree = true; } // false by default

  summary_precisiont get_precision() const { return precision; }
  unsigned get_call_location() const { return call_location; }

//  unsigned get_order() { return order; }
//  void set_order(unsigned _order) { order = _order; }

  bool is_preserved_node() const { return preserved_node; }
  bool is_preserved_edge() const { return preserved_edge; }

  void set_preserved_node() { preserved_node = true; } // false by default
  void set_preserved_edge() { preserved_edge = true; } // false by default

  unsigned get_subtree_size(const summarization_contextt& summarization_context);

  bool is_recursive(){
    for (call_sitest::iterator it = call_sites.begin();
            it != call_sites.end(); ++it)
    {
      // more presicely, it should compare pointers to target functions,
      // but in case of nondeterministically treated summaries, it would not work
      if (it->second.get_function_id() == get_function_id()) return true;
    }
    return false;
 }

  void set_recursion_nondet(bool _recursion_nondet){
    recursion_nondet = _recursion_nondet;
  }

  bool is_recursion_nondet(){
    return recursion_nondet;
  }

  void set_in_loop(bool _in_loop){
    in_loop = _in_loop;
  }

  bool is_in_loop(){
    return in_loop;
  }

private:
  call_sitest call_sites;
  location_mapt assertions;
  locationst enabled_assertions;
  irep_idt function_id;
  summary_infot *parent;
  summary_ids_sett used_summaries;
  bool assertion_in_subtree;
  summary_precisiont precision;
  unsigned call_location;
//  unsigned order;
  bool preserved_node;
  bool preserved_edge;
  bool unwind_exceeded;
  bool recursion_nondet;
  bool in_loop;
  
  void set_initial_precision(
        summary_precisiont default_precision,
        const summarization_contextt& summarization_context,
        const unsigned last_assertion_loc);
};
#endif
