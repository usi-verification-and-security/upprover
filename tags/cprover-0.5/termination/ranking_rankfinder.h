/*******************************************************************\

Module: Ranking Function Synthesis (Rankfinder backend)

Author: CM Wintersteiger

Date: May 2009

\*******************************************************************/

#ifndef CPROVER_RANKING_RANKFINDER_H_
#define CPROVER_RANKING_RANKFINDER_H_

#include <map>

#include <replace_symbol.h>

#include "ranking_base.h"

class ranking_synthesis_rankfindert:public ranking_synthesis_baset
{
public:
  ranking_synthesis_rankfindert(
    const bodyt &_body,
    const contextt &_ctx,
    contextt &_sctx,
    message_handlert &_mh):
      ranking_synthesis_baset(_body, _ctx, _sctx, _mh) {}

  virtual ~ranking_synthesis_rankfindert() {}

protected:
  std::vector<mp_integer> coefficients;
  mp_integer bound;

  typedef replace_symbolt variable_mapt;
  variable_mapt variable_map;
  contextt trans_context;

  virtual bool generate_functions(void);
  virtual exprt instantiate(void);
  bool extract_ranking_relation(void);
  void propagate_expressions(exprt &e);
  bool read_output(void);

  bool write_input_file(const exprt &e);
  void write_variables(std::ostream &f,
                       const std::set<irep_idt> &inputs,
                       const std::set<irep_idt> &outputs) const;
  bool write_constraints(std::ostream &f,
                         replace_symbolt &rmap,
                         const exprt &e);

  void collect_variables(
      exprt &e_ext,
      replace_symbolt &rmap,
      std::set<irep_idt> &inputs,
      std::set<irep_idt> &outputs);
};

#endif /* CPROVER_RANKING_RANKFINDER_H_ */
