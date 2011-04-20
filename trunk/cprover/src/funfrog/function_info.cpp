/*******************************************************************

 Module: Summarizing information associated with a single function,
 i.e., a set of discovered summaries and set of call sites.

 Author: Ondrej Sery

\*******************************************************************/

#include "function_info.h"
#include "summarization_context.h"
#include <fstream>

/*******************************************************************\

Function: function_infot::serialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_infot::serialize(std::ostream& out) const
{
  out << summaries.size() << std::endl;

  for (interpolantst::const_iterator it = summaries.begin();
          it != summaries.end();
          ++it) {

    it->serialize(out);
  }
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
    summaries.push_back(interpolantt());
    interpolantt& itp = summaries.back();

    itp.deserialize(in);
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

  in >> nfunctions;

  if (in.fail())
    return;

  for (unsigned i = 0; i < nfunctions; ++i)
  {
    std::string f_name;
    in >> f_name;

    irep_idt f_id(f_name);
    function_infost::iterator it = infos.find(f_id);

    if (it == infos.end()) {
      function_infot tmp(f_id);

      tmp.deserialize(in);
      continue;
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
  goto_functionst::function_mapt::const_iterator it =
          context.functions.function_map.find(function);
  assert (it != context.functions.function_map.end());

  const goto_programt& body = it->second.body;
  std::list<exprt> read_list;
  std::list<exprt> write_list;

  forall_goto_program_instructions(inst, body) {
    const std::list<exprt>& tmp_r = objects_read(*inst);
    read_list.insert(read_list.begin(), tmp_r.begin(), tmp_r.end());
    
    const std::list<exprt>& tmp_w = objects_written(*inst);
    write_list.insert(write_list.begin(), tmp_w.begin(), tmp_w.end());
  }

  // Accessed ids
  add_objects_to_set(ns, read_list, globals_accessed);
  add_objects_to_set(ns, write_list, globals_accessed);
  // Modified ids
  add_objects_to_set(ns, write_list, globals_modified);

  // Mark this function as analuzed
  functions_analyzed.insert(function);

  forall_goto_program_instructions(inst, body) {
    if (inst->type == FUNCTION_CALL) {

      // NOTE: Expects the function call to be a standard symbol call
      const irep_idt &target_function = to_symbol_expr(
              to_code_function_call(inst->code).function()).get_identifier();
      function_infot& target_info =
              context.function_infos.find(target_function)->second;

      if (functions_analyzed.find(target_function) == functions_analyzed.end()) {
        target_info.analyze_globals_rec(context, ns, functions_analyzed);
      }

      globals_accessed.insert(target_info.globals_accessed.begin(),
              target_info.globals_accessed.end());
      globals_modified.insert(target_info.globals_modified.begin(),
              target_info.globals_modified.end());
    }
  }

# if 1
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
    assert(ex->id() == ID_symbol);
    const irep_idt& id = to_symbol_expr(*ex).get_identifier();
    const symbolt& symbol = ns.lookup(id);

    if (symbol.static_lifetime && symbol.lvalue) {
      set.insert(id);
    }
  }
}


