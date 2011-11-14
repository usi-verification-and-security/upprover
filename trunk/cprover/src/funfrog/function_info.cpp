/*******************************************************************

 Module: Summarizing information associated with a single function,
 i.e., a set of discovered summaries and set of call sites.

 Author: Ondrej Sery

\*******************************************************************/

#include "function_info.h"
#include "summarization_context.h"
#include "expr_pretty_print.h"
#include "solvers/satcheck_opensmt.h"
#include "time_stopping.h"
#include <fstream>

//#define DEBUG_GLOBALS

/*******************************************************************\

Function: function_infot::add_summary

  Inputs:

 Outputs:

 Purpose: Adds the given summary if it is not already included or implied.
 The original parameter is cleared. Returns true if the summary was really 
 added, false if it was filtered.

\*******************************************************************/

bool function_infot::add_summary(summary_storet& summary_store,
        summary_idt summary_id, bool filter) 
{
  // Filter the new summary
  if (filter && !summaries.empty()) {
    summaryt& new_summary = summary_store.find_summary(summary_id);
    // Is implied by any older summary?
    for (summary_idst::const_iterator it = summaries.begin();
            it != summaries.end();
            ++it) {
      if (check_implies(summary_store.find_summary(*it), new_summary)) {
        summary_store.replace_summary(summary_id, *it);
        return false; // Implied by an already present summary --> skip it
      }
    }
    
    // It implies any older summary?
    unsigned used = 0;
    for (unsigned i = 0; i < summaries.size(); ++i) {
      if (check_implies(new_summary, summary_store.find_summary(summaries[i]))) {
        // Replace it
        summary_store.replace_summary(summaries[i], summary_id);
      } else {
        if (used != i) {
          // Shift needed
          std::swap(summaries[used], summaries[i]);
        }
        used++;
      }
    }
    summaries.resize(used);
  }
  
  summaries.push_back(summary_id);
  
  return true;
}

/*******************************************************************\

Function: function_infot::serialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_infot::serialize(std::ostream& out) const
{
  out << summaries.size();

  for (summary_idst::const_iterator it = summaries.begin();
          it != summaries.end();
          ++it) {

    out << " " << *it;
  }
  out << std::endl;
}

/*******************************************************************\

Function: function_infot::deserialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_infot::deserialize(std::istream& in)
{
  unsigned nsummaries;

  in >> nsummaries;

  if (in.fail())
    return;

  summaries.clear();
  summaries.reserve(nsummaries);

  for (unsigned i = 0; i < nsummaries; ++i)
  {
    summary_idt id;
    in >> id;
    summaries.push_back(id);
  }
}


/*******************************************************************\

Function: function_infot::serialize_infos

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_infot::serialize_infos(std::ostream& out, const function_infost& infos)
{
  unsigned nonempty_summaries = 0;

  for (function_infost::const_iterator it = infos.begin();
          it != infos.end();
          ++it) {
    if (it->second.get_summaries().size() > 0)
      ++nonempty_summaries;
  }
  
  out << nonempty_summaries << std::endl;

  for (function_infost::const_iterator it = infos.begin();
          it != infos.end();
          ++it) {

    if (it->second.get_summaries().size() == 0)
      continue;

    out << it->first << std::endl;
    it->second.serialize(out);
  }
}

/*******************************************************************\

Function: function_infot::deserialize_infos

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_infot::deserialize_infos(std::istream& in, function_infost& infos)
{
  unsigned nfunctions;
  std::list<function_infot> add_list;

  in >> nfunctions;

  if (in.fail())
    return;

  for (unsigned i = 0; i < nfunctions; ++i)
  {
    std::string f_name;
    in >> f_name;

    irep_idt f_id(f_name);
    function_infost::iterator it = infos.find(f_id);

    // If the function is unknown - we postpone the addition (otherwise, 
    // we could break the iterator)
    if (it == infos.end()) {
      it = infos.insert(function_infost::value_type(f_id, function_infot(f_id))).first;
    }

    it->second.deserialize(in);
  }
}

/*******************************************************************\

Function: function_infot::serialize_infos

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_infot::serialize_infos(const std::string& file, const function_infost& infos)
{
  std::ofstream out;
  out.open(file.c_str());

  if (out.fail()) {
    std::cerr << "Failed to serialize the function summaries (file: " << file <<
            " cannot be accessed)" << std::endl;
    return;
  }

  serialize_infos(out, infos);

  if (out.fail()) {
    throw "Failed to serialize the function summaries.";
  }

  out.close();
}

/*******************************************************************\

Function: function_infot::deserialize_infos

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_infot::deserialize_infos(const std::string& file, function_infost& infos)
{
  std::ifstream in;
  in.open(file.c_str());

  if (in.fail()) {
    std::cerr << "Failed to deserialize function summaries (file: " << file <<
            " cannot be read)" << std::endl;
    return;
  }

  deserialize_infos(in, infos);

  if (in.fail()) {
    throw "Failed to load function summaries.";
  }

  in.close();
}

/*******************************************************************\

Function: function_infot::analyze_globals

  Inputs:

 Outputs:

 Purpose: Fills in the sets of accessed and modified globals.

\*******************************************************************/

void function_infot::analyze_globals(summarization_contextt& context,
        const namespacet& ns)
{
  // Set of already analyzed functions
  std::set<irep_idt> functions_analyzed;

  analyze_globals_rec(context, ns, functions_analyzed);
}

/*******************************************************************\

Function: function_infot::analyze_globals_rec

  Inputs:

 Outputs:

 Purpose: Fills in the sets of accessed and modified globals using
 recursive call graph traversal. We don't handle recursion here.

\*******************************************************************/

void function_infot::analyze_globals_rec(summarization_contextt& context,
  const namespacet& ns, std::set<irep_idt>& functions_analyzed)
{
  // FIXME: Handle also recursion using fixpoint calculation!
  const goto_programt& body = context.get_function(function).body;
  std::list<exprt> read_list;
  std::list<exprt> write_list;

  forall_goto_program_instructions(inst, body) {
    const expr_listt& tmp_r = objects_read(*inst);
    read_list.insert(read_list.begin(), tmp_r.begin(), tmp_r.end());
    
    const expr_listt& tmp_w = objects_written(*inst);
    write_list.insert(write_list.begin(), tmp_w.begin(), tmp_w.end());
  }

  // Accessed ids
  add_objects_to_set(ns, read_list, globals_accessed);
  add_objects_to_set(ns, write_list, globals_accessed);
  // Modified ids
  add_objects_to_set(ns, write_list, globals_modified);

  // Mark this function as analyzed
  functions_analyzed.insert(function);

  forall_goto_program_instructions(inst, body) {
    if (inst->type == FUNCTION_CALL) {

      // NOTE: Expects the function call to be a standard symbol call
      const irep_idt &target_function = to_symbol_expr(
              to_code_function_call(inst->code).function()).get_identifier();
      function_infot& target_info = context.get_function_info(target_function);

      if (functions_analyzed.find(target_function) == functions_analyzed.end()) {
        target_info.analyze_globals_rec(context, ns, functions_analyzed);
      }

      globals_accessed.insert(target_info.globals_accessed.begin(),
              target_info.globals_accessed.end());
      globals_modified.insert(target_info.globals_modified.begin(),
              target_info.globals_modified.end());
    }
  }

# ifdef DEBUG_GLOBALS
  std::cerr << "Function: " << function << std::endl;
  std::cerr << "GLOBALs accessed" << std::endl;
  for (lex_sorted_idst::const_iterator it = globals_accessed.begin();
          it != globals_accessed.end(); ++it) {
    std::cerr << *it << std::endl;
  }
  std::cerr << "GLOBALs modified" << std::endl;
  for (lex_sorted_idst::const_iterator it = globals_modified.begin();
          it != globals_modified.end(); ++it) {
    std::cerr << *it << std::endl;
  }
# endif
}

/*******************************************************************\

Function: function_infot::add_objects_to_set

  Inputs:

 Outputs:

 Purpose: Fills in the sets of accessed and modified globals using
 recursive call graph traversal. We don't handle recursion here.

\*******************************************************************/

void function_infot::add_objects_to_set(const namespacet& ns,
        const expr_listt& exprs, lex_sorted_idst& set)
{
  forall_expr_list(ex, exprs) {
    if (ex->id() == ID_symbol) {
      const irep_idt& id = to_symbol_expr(*ex).get_identifier();
      const symbolt& symbol = ns.lookup(id);

      if (symbol.static_lifetime && symbol.lvalue) {
        set.insert(id);
      }
    } else if (ex->id() == ID_index) {
      // FIXME: This catches only simple indexing, any more involved array 
      // accesses will not be matched here.
      irep_idt id;
      if (to_index_expr(*ex).array().id() == ID_symbol) 
      {
        id = to_symbol_expr(to_index_expr(*ex).array()).get_identifier();
      } else if (to_index_expr(*ex).array().id() == ID_member && 
              to_member_expr(to_index_expr(*ex).array()).struct_op().id() == ID_symbol) 
      {
        id = to_symbol_expr(to_member_expr(
                to_index_expr(*ex).array()).struct_op()).get_identifier();
      } else {
        std::cerr << "WARNING: Unsupported indexing scheme - ignoring.";
#       ifdef DEBUG_GLOBALS
        throw "Unsupported indexing scheme.";
#       endif
        continue;
      }
      const symbolt& symbol = ns.lookup(id);

      if (symbol.static_lifetime && symbol.lvalue) {
        set.insert(id);
      }
    } else if (ex->id() == ID_member) {
      // FIXME: This catches only simple indexing, any more involved array 
      // accesses will not be matched here.
      irep_idt id;
      if (to_member_expr(*ex).struct_op().id() == ID_symbol) 
      {
        id = to_symbol_expr(to_member_expr(*ex).struct_op()).get_identifier();
      } 
      else if (to_member_expr(*ex).struct_op().id() == ID_index &&
              to_index_expr(to_member_expr(*ex).struct_op()).array().id() == ID_symbol) 
      {
        id = to_symbol_expr(to_index_expr(to_member_expr(*ex).struct_op()).array()).get_identifier();
      } 
      
      else {
        std::cerr << "WARNING: Unsupported member scheme - ignoring.";
#       ifdef DEBUG_GLOBALS
        throw "Unsupported member scheme.";
#       endif
        continue;
      }
      const symbolt& symbol = ns.lookup(id);

      if (symbol.static_lifetime && symbol.lvalue) {
        set.insert(id);
      }
    } else {
#     ifdef DEBUG_GLOBALS
      expr_pretty_print(std::cerr << "Ignoring object: ", *ex);
      std::cerr << std::endl;
#     endif
    }
  }
}

/*******************************************************************\

Function: function_infot::check_implies

  Inputs:

 Outputs:

 Purpose: Check (using a SAT call) that the first interpolant implies
 the second one (i.e., the second one is superfluous).

\*******************************************************************/

bool function_infot::check_implies(const interpolantt& first, 
        const interpolantt& second)
{
  satcheck_opensmtt prop_solver;
  contextt ctx;
  namespacet ns(ctx);

  literalt first_root;
  literalt second_root;
  literalt root;
  
  first_root = first.raw_assert(prop_solver);
  second_root = second.raw_assert(prop_solver);
  
  root = prop_solver.land(first_root, second_root.negation());
  
  prop_solver.l_set_to_true(root);

  fine_timet before, after;
  before = current_time();
  
  propt::resultt res = prop_solver.prop_solve();
  
  after = current_time();
  std::cerr << "SOLVER TIME: "<< time2string(after-before) << std::endl;
  
  if (res == propt::P_UNSATISFIABLE) {
    std::cerr << "UNSAT" << std::endl;
    return true;
  }
  std::cerr << "SAT" << std::endl;
  return false;
}

/*******************************************************************\

Function: function_infot::optimize_summaries

  Inputs:

 Outputs:

 Purpose: Finds out weather some of the given summaries are 
 superfluous, if so the second list will not contain them.

\*******************************************************************/

bool function_infot::optimize_summaries(summary_storet& summary_store, 
        const summary_idst& itps_in, summary_idst& itps_out)
{
  unsigned n = itps_in.size();
  bool changed = false;
  bool itps_map[n];
  
  // Clear the map first (i.e., no summary has been removed yet)
  for (unsigned i = 0; i < n; ++i) {
    itps_map[i] = true;
  }

  // Remove summaries which are implied by other ones
  for (unsigned i = 0; i < n; ++i) {
    // Skip already removed ones
    if (!itps_map[i])
      continue;
    
    for (unsigned j = 0; j < n; ++j) {
      if (i == j || !itps_map[j])
        continue;
      
      // Do the check
      if (check_implies(
              summary_store.find_summary(itps_in[i]), 
              summary_store.find_summary(itps_in[j]))) {
        std::cerr << "Removing summary #" << j << 
                " (implied by summary #" << i << ")" << std::endl;
        summary_store.replace_summary(itps_in[j], itps_in[i]);
        itps_map[j] = false;
        changed = true;
      }
    }
  }
  
  if (!changed)
    return false;
  
  // Prepare the new set
  for (unsigned i = 0; i < n; ++i) {
    if (itps_map[i])
      itps_out.push_back(itps_in[i]);
  }
  return true;
}

/*******************************************************************\

Function: function_infot::optimize_all_summaries

  Inputs:

 Outputs:

 Purpose: Removes all superfluous summaries.

\*******************************************************************/
void function_infot::optimize_all_summaries(summary_storet& summary_store, 
        function_infost& f_infos) 
{
  summary_idst itps_new;
  
  for (function_infost::iterator it = f_infos.begin();
          it != f_infos.end();
          ++it) {
    const summary_idst& itps = it->second.get_summaries();

    std::cerr << "--- function \"" << it->first.c_str() << "\", #summaries: " << itps.size() << std::endl;

    if (itps.size() <= 1) {
      std::cerr << std::endl;
      continue;
    }

    itps_new.clear();
    itps_new.reserve(itps.size());
    if (optimize_summaries(summary_store, itps, itps_new)) {
      it->second.set_summaries(itps_new);
    }
    
    std::cerr << std::endl;
  }
}