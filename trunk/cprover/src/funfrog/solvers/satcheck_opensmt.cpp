/*******************************************************************\

Module: OpenSMT wrapper for propositional logic. Based on
satcheck_minisat.

Author: Ondrej Sery

\*******************************************************************/

#include <assert.h>

#include <stack>
#include <literal.h>

#include <i2string.h>

#include "satcheck_opensmt.h"

#ifndef HAVE_OPENSMT
//#error "Expected HAVE_OPENSMT"
#endif

/*******************************************************************\

Function: satcheck_opensmtt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

Enode* satcheck_opensmtt::convert(const bvt &bv)
{
  Enode* tmp = NULL;
  
  for(unsigned i=0; i<bv.size(); i++) {
    const literalt& lit = bv[i];
    Enode* var = enodes[lit.var_no()];

    if (lit.sign()) {
      var = opensmt_ctx->mkCons(var, NULL);
      var = opensmt_ctx->mkNot(var);
    }

    tmp = opensmt_ctx->mkCons(var, tmp);
  }

  return tmp;
}

/*******************************************************************\

Function: satcheck_opensmtt::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt satcheck_opensmtt::l_get(literalt a) const
{
  if (a.is_true())
    return tvt(true);
  else if (a.is_false())
    return tvt(false);

  tvt tvtresult(tvt::TV_UNKNOWN);
  lbool lresult = opensmt_ctx->getModel(enodes[a.var_no()]);

  if (lresult == l_True)
    tvtresult = tvt(true);
  else if (lresult == l_False)
    tvtresult = tvt(false);
  else
    return tvtresult;
  
  if (a.sign())
    return !tvtresult;

  return tvtresult;
}

/*******************************************************************\

Function: satcheck_opensmtt::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string satcheck_opensmtt::solver_text()
{
  return "OpenSMT - propositional logic";
}

/*******************************************************************\

Function: satcheck_opensmtt::add_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_opensmtt::add_variables()
{
  enodes.reserve(no_variables());
  
  while (enodes.size() < no_variables()) {
    increase_id();
    const char* vid = id_str.c_str();
    opensmt_ctx->DeclareFun(vid, NULL, sbool);
    Enode* tmp = opensmt_ctx->mkVar(vid, true);
    enodes.push_back(tmp);
  }
}

/*******************************************************************\

Function: satcheck_opensmtt::lcnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_opensmtt::lcnf(const bvt &bv)
{
  bvt new_bv;
  Enode* tmp = NULL;
  
  if(process_clause(bv, new_bv))
    return;
    
  // Shortcut for an empty clause
  if(new_bv.empty())
  {
    tmp = opensmt_ctx->mkFalse();
    partition_root_enode = opensmt_ctx->mkCons(tmp, partition_root_enode);
    return;
  }

  add_variables();
  tmp = convert(new_bv);
  tmp = opensmt_ctx->mkOr(tmp);
  partition_root_enode = opensmt_ctx->mkCons(tmp, partition_root_enode);

  clause_counter++;
}
/*******************************************************************\

Function: satcheck_opensmtt::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt satcheck_opensmtt::prop_solve() {
  assert(status != ERROR);

  {
    std::string msg =
            i2string(_no_variables) + " variables, " +
            i2string(clause_counter) + " clauses";
    messaget::status(msg);
  }

  add_variables();

  if (partition_root_enode != NULL) {
    partition_root_enode = opensmt_ctx->mkAnd(partition_root_enode);
    opensmt_ctx->Assert(partition_root_enode);
    partition_root_enode = NULL;
  }

  std::string msg;

  opensmt_ctx->addCheckSAT();
  opensmt_ctx->executeCommands();

  if (opensmt_ctx->getStatus() == l_True) {
    msg = "SAT checker: negated claim is SATISFIABLE, i.e., does not hold";
    messaget::status(msg);
    status = SAT;
    return P_SATISFIABLE;
  } else if (opensmt_ctx->getStatus() == l_False) {
    msg = "SAT checker: negated claim is UNSATISFIABLE, i.e., holds";
    messaget::status(msg);
  } else {
    throw "Unexpected OpenSMT result.";
  }

  status = UNSAT;
  return P_UNSATISFIABLE;
}

/*******************************************************************\

Function: satcheck_opensmtt::set_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_opensmtt::set_assignment(literalt a, bool value)
{
  throw "Unsupported oparation";
}

/*******************************************************************\

Function: satcheck_opensmtt::is_in_conflict

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool satcheck_opensmtt::is_in_conflict(literalt a) const
{
  throw "Unsupported oparation";
}

/*******************************************************************\

Function: satcheck_opensmtt::set_assumptions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_opensmtt::set_assumptions(const bvt &bv)
{
  throw "Unsupported oparation";
}

/*******************************************************************\

Function: satcheck_opensmtt::increase_id

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_opensmtt::increase_id()
{
  unsigned i = 0;

  while (i < id_str.length() && id_str[i] == 'z') {
    id_str[i++] = 'a';
  }

  if (i < id_str.length()) {
    id_str[i]++;
  } else {
    id_str.append("a");
  }
}
