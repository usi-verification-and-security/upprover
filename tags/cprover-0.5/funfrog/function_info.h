/*******************************************************************

 Module: Summarizing information associated with a single function,
 i.e., a set of discovered summaries and set of call sites.

 Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_FUNCTION_INFO_H
#define CPROVER_FUNCTION_INFO_H

#include <irep.h>
#include <expr.h>
#include <hash_cont.h>

#include "solvers/interpolating_solver.h"

class function_infot;
class summarization_contextt;
typedef hash_map_cont<irep_idt, function_infot, irep_id_hash> function_infost;

// Collected summarization info for a single function
class function_infot {
public:
  function_infot() : function(ID_nil) {}
  function_infot(const irep_idt& _function) : function(_function) {}

  // Adds the given summary if it is not already included or implied.
  // The original parameter is cleared
  void add_summary(interpolantt& summary, bool filter);

  // Adds the given list of summaries. The original list is cleared
  void add_summaries(interpolantst& new_summaries, bool filter) {
    summaries.reserve(summaries.size() + new_summaries.size());
    
    for (interpolantst::iterator it = new_summaries.begin();
            it != new_summaries.end();
            ++it) {
      add_summary(*it, filter);
    }
    new_summaries.clear();
  }

  // Removes all summaries
  void clear_summaries() {
    summaries.clear();
  }

  const interpolantst& get_summaries() const { return summaries; }

  // Serialization of summaries
  void serialize(std::ostream& out) const;
  void deserialize(std::istream& in);

  static void serialize_infos(std::ostream& out, const function_infost& infos);
  static void deserialize_infos(std::istream& in, function_infost& infos);

  static void serialize_infos(const std::string& file, const function_infost& infos);
  static void deserialize_infos(const std::string& file, function_infost& infos);

  void analyze_globals(summarization_contextt& context, const namespacet& ns);

  // Helper struct with lexicographical ordering for dstring
  struct dstring_lex_ordering
  {
    bool operator()(const dstring& s1, const dstring& s2) const
    {
      return s1.compare(s2) < 0;
    }
  };

  typedef std::set<irep_idt, dstring_lex_ordering> lex_sorted_idst;
  
  const lex_sorted_idst& get_accessed_globals() const { return globals_accessed; }
  const lex_sorted_idst& get_modified_globals() const { return globals_modified; }
  
  // Removes all superfluous summaries.
  static void optimize_all_summaries(function_infost& f_infos);

private:
  // Id of the function
  irep_idt function;
  // The collected summaries
  interpolantst summaries;
  // Globals modified in the function
  lex_sorted_idst globals_modified;
  // Globals accessed (read, modified or both) in the function
  lex_sorted_idst globals_accessed;

  void analyze_globals_rec(summarization_contextt& context,
    const namespacet& ns, std::set<irep_idt>& functions_analyzed);

  static void add_objects_to_set(const namespacet& ns,
        const expr_listt& exprs, lex_sorted_idst& set);
  
  // Check (using a SAT call) that the first interpolant implies
  // the second one (i.e., the second one is superfluous).
  static bool check_implies(const interpolantt& first, 
        const interpolantt& second);
  
  // Finds out weather some of the given summaries are 
  // superfluous, if so the second list will not contain them.
  static bool optimize_summaries(const interpolantst& itps_in, 
        interpolantst& itps_out);

};


#endif