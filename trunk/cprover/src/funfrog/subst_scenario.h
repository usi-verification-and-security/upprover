/*******************************************************************

 Module: An interface between summarizing checker and summary info,
         providing a precision level for all function calls
         of the given program

 Author: Grigory Fedyukovich

\*******************************************************************/

#ifndef CPROVER_SUBST_SCENARIO_H
#define CPROVER_SUBST_SCENARIO_H

#include <map>
#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>
#include <util/xml.h>

#include "call_tree_node.h"
#include "unwind.h"

class call_tree_nodet;

enum class init_modet {
    ALL_SUBSTITUTING,
    ALL_HAVOCING
    // anything else?
};

class subst_scenariot:public unwindt {
public:
  subst_scenariot(
      const goto_functionst &goto_functions, unsigned int max_unwind):
        unwindt(max_unwind),
        functions_root (nullptr, 0),
        default_precision (INLINE),
        global_loc (0),
        goto_functions {goto_functions}
  {};

  call_tree_nodet& get_call_tree_root(){ return functions_root; };

  void get_unwinding_depth();

  void refine_recursion_call(call_tree_nodet& call);

  void process_goto_locations();
  void setup_default_precision(init_modet init);
  std::vector<call_tree_nodet*>& get_call_summaries() { return functions; }
  unsigned get_summaries_count() { return get_precision_count(SUMMARY); }
  unsigned get_nondets_count() { return get_precision_count(HAVOC); }

  unsigned get_summaries_count(call_tree_nodet& summary) { return get_precision_count(summary, SUMMARY); }
  unsigned get_nondets_count(call_tree_nodet& summary) { return get_precision_count(summary, HAVOC); }

  void initialize_call_info
          (call_tree_nodet &call_info, const goto_programt &code);

  void set_initial_precision
          (const assertion_infot & assertion, const std::function<bool(const std::string &)> & has_summary)
  {
      setup_last_assertion_loc(assertion);
      assert(functions_root.is_root());
      functions_root.set_initial_precision(default_precision, has_summary, last_assertion_loc);
  }

  void serialize(const std::string& file);
  void deserialize(const std::string& file, const goto_programt& code);

  void restore_call_info(
          call_tree_nodet &call_info, const goto_programt &code, std::vector<std::string> &data);

  unsigned get_assertion_location(goto_programt::const_targett ass)
                        { return (assertions_visited[ass]).begin()->first; }

  unsigned get_last_assertion_loc(){
    return last_assertion_loc;
  }

  bool is_single_assertion_check(){
    return single_assertion_check;
  }

  unsigned get_recursive_total(){
    return rec_count_total;
  }

  unsigned get_recursive_max(){
    return rec_count_max;
  }

  const goto_functionst & get_goto_functions() const {
      return goto_functions;
  }

  void setup_last_assertion_loc(const assertion_infot& assertion);
  bool is_assertion_in_loop(const unsigned ass_loc);
  bool is_assertion_after_return(const unsigned return_loc);
  bool is_assertion_in_loop(goto_programt::const_targett& tgt){
    return is_assertion_in_loop(get_assertion_location(tgt));
  }

private:
  call_tree_nodet functions_root;
  summary_precisiont default_precision;
  location_visitedt assertions_visited;

  std::vector<call_tree_nodet*> functions;
  std::vector<std::pair<unsigned, unsigned> > goto_ranges;
  std::vector<unsigned> goto_ranges_upwards;
  unsigned global_loc;
  unsigned last_assertion_loc;
  bool single_assertion_check;

  unsigned rec_count_max;
  unsigned rec_count_total;

  const goto_functionst & goto_functions;

  const goto_functionst::goto_functiont& get_goto_function(irep_idt fun) const;

  unsigned get_precision_count(summary_precisiont precision);
  unsigned get_precision_count(call_tree_nodet& summary, summary_precisiont precision);

  void clone_children(call_tree_nodet& call, call_tree_nodet& parent);

};

/*******************************************************************\
    Function: get_initial_mode

    Purpose: Determining the initial mode from a string.
    \*******************************************************************/

inline init_modet get_init_mode(const std::string& str)
{
    if (str == "havoc-all" || str == "0"){
        return init_modet::ALL_HAVOCING;
    } else if (str == "use-summaries" || str == "1"){
        return init_modet::ALL_SUBSTITUTING;
    } else {
        // by default
        return init_modet::ALL_SUBSTITUTING;
    }
}

#endif
