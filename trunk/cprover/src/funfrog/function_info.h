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
typedef hash_map_cont<irep_idt, function_infot, irep_id_hash> function_infost;

// Collected summarization info for a single function
class function_infot {
public:
  function_infot() : function(ID_nil) {}
  function_infot(const irep_idt& _function) : function(_function) {}

  // Adds the given summary if it is not already included or implied
  // the original parameter is cleared
  void add_summary(prop_itpt& summary) {
    // FIXME: Filter the new summaries!
    summaries.push_back(prop_itpt());
    summaries.back().swap(summary);
  }

  const interpolantst& get_summaries() const { return summaries; }

  // Serialization of summaries
  void serialize(std::ostream& out) const;
  void deserialize(std::istream& in);

  static void serialize_infos(std::ostream& out, const function_infost& infos);
  static void deserialize_infos(std::istream& in, function_infost& infos);

  static void serialize_infos(const std::string& file, const function_infost& infos);
  static void deserialize_infos(const std::string& file, function_infost& infos);

private:
  // Id of the function
  irep_idt function;
  // The collected summaries
  interpolantst summaries;
};

#endif
