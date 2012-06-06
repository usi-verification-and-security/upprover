/*******************************************************************\

Module: Ranking Function Synthesis (via quantified SMT Bitvectors)

Author: CM Wintersteiger

Date: March 2010

\*******************************************************************/

#ifndef CPROVER_TERMINATION_RANKING_SMT_H
#define CPROVER_TERMINATION_RANKING_SMT_H

#include <solvers/qbf/qdimacs_core.h>

#include "ranking_base.h"

class ranking_synthesis_smtt:public ranking_synthesis_baset
{
protected:
  exprt const_coefficient;

public:
  typedef enum { COEFFICIENTS_CONSTRAINED,
                 COEFFICIENTS_UNCONSTRAINED } coef_constraintt;

  ranking_synthesis_smtt(
    const bodyt &_body,
    const contextt &_ctx,
    contextt &_sctx,
    message_handlert &_mh,
    coef_constraintt _c_mode=COEFFICIENTS_UNCONSTRAINED) :
      ranking_synthesis_baset(_body, _ctx, _sctx, _mh),
      const_coefficient("nil"),
      constrain_mode(_c_mode) {}

  virtual ~ranking_synthesis_smtt() {}

protected:
  coef_constraintt constrain_mode;
  virtual bool generate_functions(void);

  virtual exprt instantiate(void);
  virtual exprt instantiate_polynomial(void);

  typedef std::map<exprt, exprt> coefficient_mapt;
  coefficient_mapt coefficient_map;

  typedef std::vector<std::pair<exprt,int> > c_valuest;

  bool extract_ranking_relation(boolbvt &converter);
  exprt coefficient(const exprt &expr);

  void quantify_variables(exprt &f);

  void adjust_type(typet &type) const;
};

#endif /* CPROVER_RANKING_QBF_H_ */
