/*******************************************************************\

Module: Ranking Function Synthesis (Seneschal backend)

Author: CM Wintersteiger

Date: May 2009

\*******************************************************************/

#ifndef CPROVER_RANKING_SENESCHAL_H_
#define CPROVER_RANKING_SENESCHAL_H_

#include <map>

#include "ranking_base.h"

class ranking_synthesis_seneschalt:public ranking_synthesis_baset
{
public:
  ranking_synthesis_seneschalt(
    const bodyt &_body,
    const contextt &_ctx,
    contextt &_sctx,
    message_handlert &_mh):
      ranking_synthesis_baset(_body, _ctx, _sctx, _mh),
      ranking_function("nil") {}

  virtual ~ranking_synthesis_seneschalt() {}

protected:
  typedef replace_mapt variable_mapt;
  variable_mapt variable_map;
  contextt trans_context;

  exprt ranking_function;

  mp_integer bound;

  virtual bool generate_functions(void);
  virtual exprt instantiate(void);
  bool extract_ranking_relation(exprt &rf);
  bool read_output(exprt &rf);

  bool write_input_file(const exprt &e);
  void write_variables(std::ostream &f,
                       const std::set<irep_idt> &inputs,
                       const std::set<irep_idt> &outputs) const;
  bool write_constraints(std::ostream &f,
                         replace_mapt &rmap,
                         exprt e);

  void collect_variables(
    exprt &e_ext,
    replace_mapt &rmap,
    std::set<irep_idt> &inputs,
    std::set<irep_idt> &outputs);
};

#endif /* CPROVER_RANKING_RANKFINDER_H_ */
