/*******************************************************************\

Module: Ranking Function Synthesis (Complete QBF Synthesis)

Author: CM Wintersteiger

Date: October 2008

\*******************************************************************/

#ifndef CPROVER_TERMINATION_RANKING_QBF_COMPLETE_H
#define CPROVER_TERMINATION_RANKING_QBF_COMPLETE_H

#include <std_expr.h>
#include <i2string.h>
#include <simplify_expr.h>
#include <arith_tools.h>

#include <langapi/language_util.h>

#include <ansi-c/c_types.h>

#include "ranking_qbf.h"

class ranking_synthesis_qbf_completet:public ranking_synthesis_qbft
{
public:
  ranking_synthesis_qbf_completet(
    const bodyt &_body,
    const contextt &_ctx,
    contextt &_sctx,
    message_handlert &_mh):
      ranking_synthesis_qbft(_body, _ctx, _sctx, _mh),
      value_width(3)
      {}

  virtual ~ranking_synthesis_qbf_completet() {}

protected:
  virtual bool generate_functions(void);
  virtual exprt instantiate(void);

  typedef std::map<exprt, exprt> rank_function_mapt;
  rank_function_mapt rank_function_map; // .second is a ranking function

  typedef std::map<exprt, exprt> value_variable_mapt;
  value_variable_mapt value_variable_map;

  unsigned value_width;
  exprt refinement;

  exprt value_variable(const exprt &expr);
  exprt extract_ranking_relation(void);

  bool extract_functions(
    const exprt &templ,
    boolbvt &converter,
    qdimacs_coret &solver);

  void quantify_variables(boolbvt &converter, qdimacs_coret &solver);

  qdimacs_coret::resultt qbf_solve_inc(const exprt &templ);

  bool skolem_equality(void);

};

#endif /* CPROVER_RANKING_QBF_COMPLETE_H_ */
