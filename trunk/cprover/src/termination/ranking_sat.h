/*******************************************************************\

Module: Ranking Function Synthesis (SAT Enumeration)

Author: CM Wintersteiger

Date: October 2008

\*******************************************************************/

#ifndef CPROVER_TERMINATION_RANKING_SAT_H
#define CPROVER_TERMINATION_RANKING_SAT_H

#include <solvers/sat/satcheck.h>

#include "ranking_base.h"

class ranking_synthesis_satt:public ranking_synthesis_baset
{
public:
  ranking_synthesis_satt(
    const bodyt &_body,
    const contextt &_ctx,
    contextt &_sctx,
    message_handlert &_mh):
      ranking_synthesis_baset(_body, _ctx, _sctx, _mh) { }

  virtual ~ranking_synthesis_satt() {}

protected:  
  virtual bool generate_functions(void);
  virtual exprt instantiate(void);

  typedef std::map<exprt, exprt> coefficient_mapt;
  coefficient_mapt coefficient_map;

  typedef std::vector<std::pair<exprt,int> > c_valuest;

  satcheckt::resultt
      check_for_counterexample(const exprt &templ, c_valuest &c_values,
                               fine_timet &conversion_time,
                               fine_timet &solver_time);

  void show_counterexample(boolbvt &converter);

  exprt coefficient(const exprt &expr);

  void initialize_coefficients(c_valuest &c_values) const;
  bool increase_coefficients(c_valuest &c_values) const;
  void show_coefficients(c_valuest &c_values);

  void adjust_type(typet &type) const;
};

#endif /* CPROVER_RANKING_SAT_H_ */
