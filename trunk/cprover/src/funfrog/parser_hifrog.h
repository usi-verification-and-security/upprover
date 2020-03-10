/*******************************************************************\

Module: Command Line Parsing

\*******************************************************************/

#ifndef PARSER_HIFROG_H
#define PARSER_HIFROG_H


#include "version.h"
#include "parser.h"

#define HIFROG_OPTIONS \
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
  "(partial-loops)" \
  "(function):"

class parser_hifrogt : public parser_baset
{
public:
    parser_hifrogt(int argc, const char **argv):
            parser_baset(HIFROG_OPTIONS,std::string("HIFROG ") + HIFROG_VERSION,  argc, argv)
    {
    }
  int doit() override;
  void help() override;
  
};


#endif
