/*******************************************************************\

Module: Command Line Parsing

\*******************************************************************/

#ifndef PARSER_HIFROG_H
#define PARSER_HIFROG_H

#include <fstream>
#include <cstdlib>

#include <util/options.h>
#include "xml_interface.h"

#include <goto-programs/goto_trace.h>

#include <util/ui_message.h>
#include <util/parse_options.h>

//#include <goto-programs/goto_functions.h>

#include <goto-programs/goto_model.h>
#include "check_claims.h"

#define FUNFROG_OPTIONS \
  "D:I:(16)(32)(64)(v):(version)" \
  "(i386-linux)(i386-macos)(ppc-macos)" \
  "(show-goto-functions)(show-fpfreed-program)(show-dereferenced-program)" \
  "(save-program)(save-fpfreed-program)(save-dereferenced-program)" \
  "(show-transformed-program)(show-inlined-program)" \
  "(save-transformed-program)(save-inlined-program)" \
  "(show-claimed-program)(show-abstracted-program)" \
  "(save-claimed-program)(save-abstracted-program)" \
  "(save-summaries):(load-summaries):" \
  "(save-omega):(load-omega):" \
  "(load-sum-model):" \
  "(save-omega):(load-omega):" \
  "(show-symbol-table)(show-value-sets)" \
  "(save-claims)" \
  "(xml-ui)(xml-interface)" \
  "(no-slicing)(no-assert-grouping)(no-summary-optimization)" \
  "(pointer-check)(bounds-check)(div-by-zero-check)(overflow-check)(nan-check)" \
  "(string-abstraction)(assertions)" \
  "(show-pass)(suppress-fail)(no-progress)" \
  "(show-claims)(claims-count)(all-claims)(claims-opt):(claim):(claimset):" \
  "(theoref)(force)(custom):(heuristic):(bitwidth):" \
  "(sum-theoref)" \
  "(init-upgrade-check)(do-upgrade-check):" \
  "(save-queries)(save-change-impact):" \
  "(tree-interpolants)(proof-trans):(reduce-proof)(reduce-proof-time):(reduce-proof-loops):(reduce-proof-graph):(color-proof):" \
  "(random-seed):(no-partitions)(no-itp)(verbose-solver):" \
  "(itp-algorithm): (itp-uf-algorithm): (itp-lra-algorithm):(itp-lra-factor): (check-itp): (part-itp):" \
  "(unwind):(unwindset):" \
  "(type-constraints):(type-byte-constraints):" \
  "(inlining-limit):(testclaim):" \
  "(pobj)(eq)(neq)(ineq)" \
  "(no-error-trace)" \
  "(no-cex-model)" \
  "(no-sum-refine)" \
  "(refine-mode):(init-mode):(logic):(list-templates)"\
  "(solver):(dump-query)(dump-pre-query)(dump-SSA-tree)(dump-query-name):"\
  "(partial-loops)"

class parser_hifrogt:
  public parse_options_baset,
  public xml_interfacet,
  public messaget
{
public:
  int doit() override;
  void help() override;

  parser_hifrogt(int argc, const char **argv);

protected:
//goto_modelt goto_model;   //SA: removed it from this class to allow the possibility of having
                             //several goto-models in parsing stage(for e.g, we need it in upgrade-check)

  ui_message_handlert ui_message_handler; // KE: due to change from register_languages to messaget

  unsigned claim_user_nr = 0;
  claim_numberst claim_numbers;
  claim_checkmapt claim_checkmap;

  void register_languages();
  void get_command_line_options(optionst &);
  void set_default_options(optionst &);

  unsigned count(const goto_functionst &goto_functions) const;
  unsigned count(const goto_programt &goto_program) const;

//move it outside of this class to be a standalone function for processing several goto-model in a single run
//bool process_goto_program(const optionst &);

  bool get_goto_program(goto_modelt &, cmdlinet &);
  void calculate_show_claims(goto_modelt &, claim_numberst &, claim_checkmapt &);
  bool validate_input_options (const claim_numberst &, unsigned &);
  void trigger_upgrade_check(const goto_modelt &);
  void set_options(const cmdlinet &cmdline);
  void eval_verbosity();

  optionst options;
  std::ofstream statfile;

private:
  void cbmc_error_interface(std::string error_msg) { error() << error_msg << eom; }
  void cbmc_status_interface(std::string msg) { status() << msg << eom; }
};

//Declaration:
// A standalone function; originally it was a member function of above class
bool process_goto_program(const cmdlinet &cmdline, const optionst &, goto_modelt &goto_model,
                          messaget &message);

#endif
