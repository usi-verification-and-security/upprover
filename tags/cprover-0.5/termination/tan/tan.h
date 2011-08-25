/*******************************************************************\

Module: Command Line Parsing

Author: CM Wintersteiger

\*******************************************************************/

#ifndef CPROVER_TAN_PARSEOPTIONS_H
#define CPROVER_TAN_PARSEOPTIONS_H

#include <fstream>

#include <langapi/language_ui.h>
#include <ui_message.h>
#include <parseoptions.h>

#include <options.h>
#include <context.h>

#include <goto-programs/goto_functions.h>
#include <pointer-analysis/value_set_analysis.h>
#include <goto-programs/invariant_propagation.h>

#define TAN_OPTIONS \
  "D:I:(16)(32)(64)(v):(version)" \
  "(show-model)(show-preprocessed-model)" \
  "(function)(claim):(show-claims)" \
  "(string-abstraction)(no-invariant-propagation)(no-value-sets)" \
  "(no-loop-slicing)" \
  "(ranksynthesis):" \
  "(unranked-method):" \
  "(engine):"

typedef enum { TAN_UNKNOWN=0, 
               TAN_TERMINATING=10,
               TAN_NONTERMINATING=20, 
               TAN_ERROR=30 } tan_resultt;

class tant:
  public parseoptions_baset,
  public language_uit
{
public:
  virtual int doit();
  virtual void help();

  tant(int argc, const char **argv);
  
private:
  contextt context;
  namespacet ns;
  goto_functionst goto_functions;
  
  // some stats
  unsigned loops_nonterminating;
  
  bool check_and_set_options(void);
  bool from_file(const std::string &filename);
  bool preprocess(void);
  tan_resultt analyze(void);
  
  bool get_entry_point(
    goto_functionst::function_mapt::const_iterator &func_it,
    goto_programt::const_targett &entry);
  
  goto_programt::const_targett find_next_loop(
    goto_programt::const_targett current,
    const goto_programt &program,
    std::list<goto_programt::const_targett> &recursion_stack) const;
};

#endif
