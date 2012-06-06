/*******************************************************************\

Module: Ranking Function Synthesis (QBF Bitwise Coefficient Synthesis)

Author: CM Wintersteiger

Date: May 2009

\*******************************************************************/

#ifndef CPROVER_TERMINATIIN_RANKING_QBF_BITWISE_H
#define CPROVER_TERMINATION_RANKING_QBF_BITWISE_H

#include "ranking_qbf.h"

class ranking_synthesis_qbf_bitwiset:public ranking_synthesis_qbft
{
public:
  typedef enum { F_NOTHING,
                 F_PROJECTIONS,
                 F_AFFINE,
                 F_CONJUNCTIVE,
                 F_DISJUNCTIVE } function_classt;

  ranking_synthesis_qbf_bitwiset(
    const bodyt &_body,
    const contextt &_ctx,
    contextt &_sctx,
    message_handlert &_mh,
    function_classt mode=F_AFFINE) :
      ranking_synthesis_qbft(_body, _ctx, _sctx, _mh),
      function_class(mode),
      bitwise_width(1) {}

  virtual ~ranking_synthesis_qbf_bitwiset() {}

  void set_mode(function_classt m) { function_class=m; }

protected:
  function_classt function_class;
  unsigned bitwise_width;

  virtual bool generate_functions(void);

  virtual exprt instantiate(void);
  virtual exprt instantiate_nothing(void);

  virtual exprt instantiate_projections(void);
  virtual exprt instantiate_affine(void);
  virtual exprt instantiate_conjunctive(void);
  virtual exprt instantiate_disjunctive(void);

  bool extract_ranking_relation(boolbvt &converter);

  exprt coefficient(const exprt &expr);

  void quantify_variables(boolbvt &converter, qdimacs_coret &solver);

  exprt bitwise_chain(const irep_idt &op, const exprt &expr) const;
  std::pair<exprt,exprt> affine_template(const irep_idt &termOp,
                                         const irep_idt &coefOp);
  
  std::pair<exprt,exprt> ite_template(void);

  std::pair<exprt,exprt> duplicate(const std::pair<exprt,exprt> pp,
                                   unsigned bits);
  
  unsigned get_state_size(void) const;
};

#endif /* RANKING_QBF_BITWISE_H_ */
