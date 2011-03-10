/*******************************************************************\

Module: OpenSMT wrapper for propositional logic. Based on
satcheck_minisat.

Author: Ondrej Sery

\*******************************************************************/

#include <assert.h>

#include <i2string.h>

#include "satcheck_opensmt.h"

#ifndef HAVE_OPENSMT
//#error "Expected HAVE_OPENSMT"
#endif

#define MAX_OPENSMT_PARTITIONS 63

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

Function: satcheck_opensmtt::new_partition

  Inputs:

 Outputs: returns a unique partition id

 Purpose: Begins a partition of formula for latter reference during
 interpolation extraction. All assertions made until
 next call of new_partition() will be part of this partition.

\*******************************************************************/
fle_part_idt satcheck_opensmtt::new_partition()
{
  assert(partition_count == 0 || partition_root_enode != NULL);
  
  // Finish the previous partition if any
  if (partition_count > 0)
    close_partition();

  if (partition_count == MAX_OPENSMT_PARTITIONS) {
    std::string s =
            "OpenSMT does not support more than " +
            i2string(MAX_OPENSMT_PARTITIONS) + "partitions so far.";
    throw s.c_str();
  }

  return partition_count++;
}


/*******************************************************************\

Function: satcheck_opensmtt::get_interpolant

  Inputs:

 Outputs:

 Purpose: Extracts the symmetric interpolant of the specified set of
 partitions. This method can be called only after solving the
 the formula with an UNSAT result.

\*******************************************************************/
void satcheck_opensmtt::get_interpolant(const interpolation_taskt& partition_ids,
    std::vector<prop_itpt>& interpolants) const
{
  std::vector<Enode*> itp_enodes;
  itp_enodes.reserve(partition_ids.size());

  opensmt_ctx->GetInterpolants(partition_ids, itp_enodes);

  for (std::vector<Enode*>::iterator it = itp_enodes.begin();
          it != itp_enodes.end(); ++it) {
    Enode* node = (*it);

    std::cout << "OpenSMT interpolant: ";
    node->print(std::cout);
    std::cout << std::endl;

    prop_itpt itp;
    extract_itp(node, itp);

    std::cout << "CProver stored interpolant: ";
    itp.print(std::cout);

    interpolants.push_back(prop_itpt());
    interpolants.back().swap(itp);
  }
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
    assert (decode_id(vid) == enodes.size()-1);
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
    close_partition();
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
  throw "Unsupported operation";
}

/*******************************************************************\

Function: satcheck_opensmtt::is_in_conflict

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool satcheck_opensmtt::is_in_conflict(literalt a) const
{
  throw "Unsupported operation";
}

/*******************************************************************\

Function: satcheck_opensmtt::set_assumptions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_opensmtt::set_assumptions(const bvt &bv)
{
  throw "Unsupported operation";
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

  std::cout << id_str << std::endl;
}

/*******************************************************************\

Function: satcheck_opensmtt::decode_id

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned satcheck_opensmtt::decode_id(const char* id) const
{
  unsigned base = 1;
  unsigned i = 0;

  while (*id != 0) {
    i += base * (*id++ - 'a' + 1);
    base *= 'z'-'a'+1;
  }
  return i-1;
}

/*******************************************************************\

Function: satcheck_opensmtt::close_partition

  Inputs:

 Outputs:

 Purpose: Closes the interpolation partition by passing its CNF form
 (collected in partition_root_enode) to the solver.

\*******************************************************************/

void satcheck_opensmtt::close_partition()
{
  partition_root_enode = opensmt_ctx->mkAnd(partition_root_enode);
  opensmt_ctx->Assert(partition_root_enode);
  partition_root_enode = NULL;
}

/*******************************************************************\

Function: satcheck_opensmtt::extract_itp

  Inputs:

 Outputs:

 Purpose: Extracts the propositional interpolant from the OpenSMT
 E-node representation.

\*******************************************************************/

void satcheck_opensmtt::extract_itp(const Enode* enode,
  prop_itpt& target_itp) const
{
  enode_cachet cache;
  target_itp.set_no_original_variables(_no_variables);
  target_itp.root_literal = extract_itp_rec(enode, target_itp, cache);
}

/*******************************************************************\

Function: satcheck_opensmtt::extract_itp_rec

  Inputs:

 Outputs:

 Purpose: Extracts the propositional interpolant from the OpenSMT
 E-node representation. Simple recursive implementation.

\*******************************************************************/

literalt satcheck_opensmtt::extract_itp_rec(const Enode* enode,
  prop_itpt& target_itp, enode_cachet enode_cache) const
{
  enode_cachet::const_iterator cached_it = enode_cache.find(enode->getId());
  literalt result;

  if (cached_it != enode_cache.end()) {
    return cached_it->second;
  }

  if (enode->isTerm()) {
    switch (enode->getCar()->getId()) {
    case ENODE_ID_TRUE:
      result = const_literal(true);
      break;
    case ENODE_ID_FALSE:
      result = const_literal(false);
      break;
    case ENODE_ID_AND:
      assert(enode->getArity() == 2);
      result = target_itp.land(
              extract_itp_rec(enode->get1st(), target_itp, enode_cache),
              extract_itp_rec(enode->get2nd(), target_itp, enode_cache));
      break;
    case ENODE_ID_OR:
      assert(enode->getArity() == 2);
      result = target_itp.lor(
              extract_itp_rec(enode->get1st(), target_itp, enode_cache),
              extract_itp_rec(enode->get2nd(), target_itp, enode_cache));
      break;
    case ENODE_ID_NOT:
      assert(enode->getArity() == 1);
      result = target_itp.lnot(
              extract_itp_rec(enode->get1st(), target_itp, enode_cache));
      break;
    default:
      if (enode->isAtom()) {
        // Atom must be a prop. variable
        assert(enode->getArity() == 0 && enode->getCar()->isSymb());
        result.set(decode_id(enode->getCar()->getNameFullC()), false);
      } else {
        throw "Unexpected Enode term type in the interpolant.";
      }
    }
  } else {
    throw "Unexpected Enode type in the interpolant.";
  }

  enode_cache.insert(enode_cachet::value_type(enode->getId(), result));
  return result;
}
