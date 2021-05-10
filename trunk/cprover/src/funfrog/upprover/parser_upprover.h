#ifndef PARSER_UPPROVER_H
#define PARSER_UPPROVER_H

#include "funfrog/parser.h"
#include "funfrog/version.h"

#define UPPROVER_OPTIONS \
  "D:I:(16)(32)(64)(v):(version)" \
  "(i386-linux)(i386-macos)(ppc-macos)" \
  "(show-goto-functions)(show-fpfreed-program)(show-dereferenced-program)" \
  "(save-summaries):(load-summaries):" \
  "(save-omega):(load-omega):" \
  "(show-symbol-table)(show-value-sets)" \
  "(save-claims)" \
  "(show-claims)(claims-count)(all-claims)(claims-opt):(claim):(claimset):" \
  "(bootstrapping)(TIP-check)(summary-validation):" \
  "(sum-theoref)" \
  "(save-queries)(save-change-impact):" \
  "(tree-interpolants)(proof-trans):(reduce-proof)(reduce-proof-time):(reduce-proof-loops):(reduce-proof-graph):(color-proof):" \
  "(random-seed):(no-partitions)(no-itp)(verbose-solver):" \
  "(itp-algorithm): (itp-uf-algorithm): (itp-lra-algorithm):(itp-lra-factor): (check-itp): (part-itp):" \
  "(unwind):(unwindset):" \
  "(type-constraints):(type-byte-constraints):" \
  "(inlining-limit):(testclaim):" \
  "(no-error-trace)" \
  "(no-cex-model)" \
  "(refine-mode):(init-mode):(logic):(list-templates)"\
  "(solver):(dump-query)(dump-pre-query)(dump-SSA-form)(dump-query-name):"\
  "(function):"


class parser_upprovert : public parser_baset {

public:
    parser_upprovert(int argc, const char **argv) :
        parser_baset(UPPROVER_OPTIONS + std::string("UPPROVER ") + UPPROVER_VERSION,  argc, argv)
    {
    }
    
    int doit() override;
    void help() override;

protected:
    void trigger_upprover(const goto_modelt &goto_model_old);
};

#endif //PARSER_UPPROVER_H
