/*******************************************************************

 Module: Summarizing information associated with a single function,
 i.e., a set of discovered summaries and set of call sites.

 Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_FUNCTION_INFO_H
#define CPROVER_FUNCTION_INFO_H

#include <util/irep.h>
#include <util/expr.h>
#include <set>

#include "summary_store_fwd.h"

class summarization_contextt;
class smt_summary_storet;
class namespacet;
class itpt;

typedef itpt interpolantt;

// Collected summarization info for a single function
class function_infot {
public:
  function_infot() : function(ID_nil) {}
  function_infot(const irep_idt& _function) : function(_function) {}

  // Adds the given summary if it is not already included or implied.
  // The original parameter is cleared. Returns true if the summary was really 
  // added, false if it was filtered.
  bool add_summary(summary_storet& summary_store, summary_idt summary, 
          bool filter);

  const summary_idst& get_summaries() const { return summaries; }

  // Serialization of summaries
  void serialize(std::ostream& out) const;
  void deserialize(std::istream& in);
  void deserialize(unsigned);
  
  static void serialize_infos(std::ostream& out, const function_infost& infos);
  static void deserialize_infos(std::istream& in, function_infost& infos);
  static void deserialize_infos(smt_summary_storet* store, function_infost& infos); // for SMT version only

  static void serialize_infos(const std::string& file, const function_infost& infos);
  static void deserialize_infos(const std::string& file, function_infost& infos);

  void analyze_globals(summarization_contextt& context, const namespacet& ns);

  // Helper struct with lexicographical ordering for dstring
  struct dstring_lex_ordering
  {
    bool operator()(const dstringt& s1, const dstringt& s2) const
    {
      return s1.compare(s2) < 0;
    }
  };

  typedef std::set<irep_idt, dstring_lex_ordering> lex_sorted_idst;
  
  const lex_sorted_idst& get_accessed_globals() const { return globals_accessed; }
  const lex_sorted_idst& get_modified_globals() const { return globals_modified; }
  
  // Removes all superfluous summaries.
  static void optimize_all_summaries(summary_storet& summary_store, 
        function_infost& f_infos);

  // Removes all summaries
  void clear_summaries() { summaries.clear(); }
   // Id of the function
  irep_idt function;

private:
  // The collected summaries
  summary_idst summaries;
  // Globals modified in the function
  lex_sorted_idst globals_modified;
  // Globals accessed (read, modified or both) in the function
  lex_sorted_idst globals_accessed;

  void analyze_globals_rec(summarization_contextt& context,
    const namespacet& ns, std::set<irep_idt>& functions_analyzed);

  // Add global variables to the set
  static void add_to_set_if_global(const namespacet& ns,
        const exprt& ex, lex_sorted_idst& set);
  
  static void add_objects_to_set(const namespacet& ns,
        const expr_listt& exprs, lex_sorted_idst& set);
  
  // Check (using a SAT call) that the first interpolant implies
  // the second one (i.e., the second one is superfluous).
  /*
  static bool check_implies_prop(const prop_interpolantt& first, 
        const prop_interpolantt& second);
  static bool check_implies_smt(const smt_interpolantt& first, 
        const smt_interpolantt& second);
   */
  static bool check_implies(const interpolantt& first, const interpolantt& second);
  
  // Finds out weather some of the given summaries are 
  // superfluous, if so the second list will not contain them.
  static bool optimize_summaries(summary_storet& summary_store, 
        const summary_idst& itps_in, summary_idst& itps_out);

  // Set of summaries is assigned the given set. The input set is assigned the
  // old set of summaries.
  void set_summaries(summary_idst& new_summaries)
  {
    summaries.swap(new_summaries);
  }

 
  friend class summary_storet;
};


#endif
