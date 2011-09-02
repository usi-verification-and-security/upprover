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

#include "summary_info.h"
#include "summarization_context.h"

class subst_scenariot {
public:
  subst_scenariot(
      const summarization_contextt &_summarization_context,
      const goto_programt &goto_program):
        summarization_context (_summarization_context),
        functions_root (NULL),
        default_precision (INLINE),
        functions (NULL),
        goto_ranges (NULL),
        global_loc (0)
  {
    initialize_summary_info (functions_root, goto_program);
  };

  summary_infot& get_summary_info(){ return functions_root; };

  void process_goto_locations();
  void setup_default_precision(init_modet init);
  std::vector<call_summaryt*>& get_call_summaries() { return functions; }
  unsigned get_summaries_count() { return get_precision_count(SUMMARY); }
  unsigned get_nondets_count() { return get_precision_count(HAVOC); }

  void initialize_call
      (call_summaryt& call_summary, const irep_idt &target_function);

  void initialize_summary_info
      (summary_infot& summary_info, const goto_programt& code);

  void set_initial_precision
      (const assertion_infot& assertion, bool assert_grouping)
  {
      functions_root.set_initial_precision(default_precision,// assertions,
          summarization_context, assertion, assert_grouping);
  }

private:
  const summarization_contextt &summarization_context;
  summary_infot functions_root;
  summary_precisiont default_precision;
//  location_mapt assertions;

  std::vector<call_summaryt*> functions;
  std::vector<std::pair<unsigned, unsigned> > goto_ranges;
  unsigned global_loc;

  unsigned get_precision_count(summary_precisiont precision);
};

#endif