/*******************************************************************\

Module: Wrapper for OpenSMT2. Based on satcheck_minisat.

Author: Grigory Fedyukovich

\*******************************************************************/

#include "smtcheck_opensmt2.h"

void smtcheck_opensmt2t::initializeSolver()
{
  osmt = new Opensmt(opensmt_logic::qf_uf); // GF: hardcode for now
  logic = &(osmt->getLogic());
  mainSolver = &(osmt->getMainSolver());
  const char* msg;
  osmt->getConfig().setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
}

// Free all resources related to OpenSMT2
void smtcheck_opensmt2t::freeSolver()
{
  if (osmt != NULL) delete osmt;
}

/*******************************************************************\

Function: smtcheck_opensmt2t::new_partition

  Inputs:

 Outputs: returns a unique partition id

 Purpose: Begins a partition of formula for latter reference during
 interpolation extraction. All assertions made until
 next call of new_partition() will be part of this partition.

\*******************************************************************/
fle_part_idt smtcheck_opensmt2t::new_partition()
{
//Allowing partitions for havoced functions and fully slices ones

  assert(partition_count == 0 || current_partition != NULL);
  if (partition_count != 0 && current_partition == NULL) {
    std::cerr << "WARNING: last partition was empty (probably due to slicing)." << std::endl;
    // NOTE: The index is reused for the next partition, outer context must
    // ensure that the previously returned index is not used.
    partition_count--;
  }
  
  // Finish the previous partition if any
  if (current_partition != NULL)
    close_partition();

  current_partition = new vec<PTRef>();

  return partition_count++;
}


literalt smtcheck_opensmt2t::new_variable()
{
  literalt l;
  l.set(no_literals, false);
  no_literals++;
  return l;
}

// TODO: enhance this to get assignments for any PTRefs, not only for Bool Vars.
tvt smtcheck_opensmt2t::get_assignemt(literalt a) const
{
  if (a.is_true())
    return tvt(true);
  else if (a.is_false())
    return tvt(false);

  tvt tvtresult(tvt::TV_UNKNOWN);
  ValPair a_p = mainSolver->getValue(literals[a.var_no()]);
  lbool lresult = (*a_p.val == *true_str) ? l_True : l_False;

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


literalt smtcheck_opensmt2t::convert(const exprt &expr)
{
	literalt l;
	if(expr.id()==ID_symbol){
		// converting callstart / callend literals
		string str = id2string(to_symbol_expr(expr).get_identifier());
		PTRef var = logic->mkBoolVar(str.c_str());
		l = new_variable();
		literals.push_back (var);
	} else {
		// unsupported so far
	}
    return l;
}

void smtcheck_opensmt2t::set_to_true(const exprt &expr)
{
	// here should be smth like
	// PTRef p;
	// encode p
	// current_partition->push(p);

}

void smtcheck_opensmt2t::set_equal(literalt l1, literalt l2){
	//GF: hack for now
}

literalt smtcheck_opensmt2t::limplies(literalt l1, literalt l2){
	//GF: hack for now
	literalt l;
	return l;
}

literalt smtcheck_opensmt2t::land(literalt l1, literalt l2){
	//GF: hack for now
	literalt l;
	return l;
}

literalt smtcheck_opensmt2t::land(bvt b){
	//GF: hack for now
	literalt l;
	return l;
}

literalt smtcheck_opensmt2t::lor(literalt l1, literalt l2){
	//GF: hack for now
	literalt l;
	return l;
}

literalt smtcheck_opensmt2t::lor(bvt b){
	//GF: hack for now
	literalt l;
	return l;
}

literalt smtcheck_opensmt2t::lnot(literalt l){
	//GF: hack for now
	return l;
}


void smtcheck_opensmt2t::extract_itp(PTRef ptref,
  prop_itpt& target_itp) const
{
  ptref_cachet cache;
//  target_itp.set_no_original_variables(no_literals);
  target_itp.root_literal = extract_itp_rec(ptref, target_itp, cache);
}

// GF: this all should be rewritten, prop_itpt should be replaces by theory_itpt
//     or, maybe, we can extract interpolants straight to CProver exprt?
literalt smtcheck_opensmt2t::extract_itp_rec(PTRef ptref,
  prop_itpt& target_itp, ptref_cachet& ptref_cache) const
{
  ptref_cachet::const_iterator cached_it = ptref_cache.find(ptref);
  literalt result;

  if (cached_it != ptref_cache.end()) {
    return cached_it->second;
  }

  if(logic->getTerm_true() == ptref){
      result = const_literal(true);
  }
  else if(logic->getTerm_false() == ptref){
      result = const_literal(false);
  }
  else if(logic->isAnd(ptref))
  {
      Pterm& ptm = logic->getPterm(ptref);
      assert(ptm.size() >= 2);
      result = target_itp.land(
              extract_itp_rec(ptm[0], target_itp, ptref_cache),
              extract_itp_rec(ptm[1], target_itp, ptref_cache));
      for(int i = 2; i < ptm.size(); ++i)
          result = target_itp.land(result, extract_itp_rec(ptm[i], target_itp, ptref_cache));
  }
  else if(logic->isOr(ptref))
  {
      Pterm& ptm = logic->getPterm(ptref);
      assert(ptm.size() >= 2);
      result = target_itp.lor(
              extract_itp_rec(ptm[0], target_itp, ptref_cache),
              extract_itp_rec(ptm[1], target_itp, ptref_cache));
      for(int i = 2; i < ptm.size(); ++i)
          result = target_itp.lor(result, extract_itp_rec(ptm[i], target_itp, ptref_cache));
  }
  else if(logic->isNot(ptref))
  {
      Pterm& ptm = logic->getPterm(ptref);
      assert(ptm.size() == 1);
      result = target_itp.lnot(
              extract_itp_rec(ptm[0], target_itp, ptref_cache));
  }
  else
  {
      Pterm& ptm = logic->getPterm(ptref);
      assert(ptm.size() == 0);
//      result.set(decode_id(logic->getSymName(ptref)), false);
      //GF: hack
  } 
    
  ptref_cache.insert(ptref_cachet::value_type(ptref, result));
  return result;
}

// helper interpolation method taken from opensmt
void smtcheck_opensmt2t::produceConfigMatrixInterpolants (const vector< vector<int> > &configs, vector<PTRef> &interpolants)
{
  SimpSMTSolver& solver = osmt->getSolver();

  // First interpolant is true -> all partitions in B
  for ( unsigned i = 0; i < configs.size(); i++ )
  {
    ipartitions_t mask = 0;
    for (unsigned j = 0; j < configs[i].size(); j++)
    {
      // Set partitions[i] bit to 1 (starting from bit 1, bit 0 is untouched)
      setbit ( mask, configs[i][j] + 1);
    }

    solver.getSingleInterpolant(interpolants, mask);
  }
}

/*******************************************************************\

Function: smtcheck_opensmt2t::get_interpolant

  Inputs:

 Outputs:

 Purpose: Extracts the symmetric interpolant of the specified set of
 partitions. This method can be called only after solving the
 the formula with an UNSAT result.

\*******************************************************************/
void smtcheck_opensmt2t::get_interpolant(const interpolation_taskt& partition_ids,
    interpolantst& interpolants)
{
  assert(ready_to_interpolate);

  // Set labeling function
  const char* msg;
  osmt->getConfig().setOption(SMTConfig::o_itp_bool_alg, SMTOption(itp_algorithm), msg);

  SimpSMTSolver& solver = osmt->getSolver();

  // Create the proof graph
  solver.createProofGraph();

  vector<PTRef> itp_ptrefs;

  // iterative call of getSingleInterpolant:
  produceConfigMatrixInterpolants(partition_ids, itp_ptrefs);

  solver.deleteProofGraph();

  for(unsigned i = 0; i < itp_ptrefs.size(); ++i)
  {
      prop_itpt itp;
      extract_itp(itp_ptrefs[i], itp);
      interpolants.push_back(prop_itpt());
      interpolants.back().swap(itp);
  }
}


/*******************************************************************\

Function: smtcheck_opensmt2t::can_interpolate

  Inputs:

 Outputs:

 Purpose: Is the solver ready for interpolation? I.e., the solver was used to 
 decide a problem and the result was UNSAT

\*******************************************************************/
bool smtcheck_opensmt2t::can_interpolate() const
{
  return ready_to_interpolate;
}


/*******************************************************************\

Function: smtcheck_opensmt2t::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool smtcheck_opensmt2t::solve() {

  if (dump_queries){
    char* msg1;
    mainSolver->writeSolverState_smtlib2("__SMT_query", &msg1);
  }

  ready_to_interpolate = false;

  if (current_partition != NULL) {
    close_partition();
  }

//  add_variables();

  sstat r = mainSolver->check();

  if (r == s_True) {
    return true;
  } else if (r == s_False) {
    ready_to_interpolate = true;
  } else {
    throw "Unexpected OpenSMT result.";
  }

  return false;
}


/*******************************************************************\

Function: smtcheck_opensmt2t::close_partition

  Inputs:

 Outputs:

 Purpose: Closes the interpolation partition by passing its CNF form
 (collected in current_partition) to the solver.

\*******************************************************************/

void smtcheck_opensmt2t::close_partition()
{
  assert(current_partition != NULL);
  if (partition_count > 0){
    if (current_partition->size() > 1){
      mainSolver->push(logic->mkAnd(*current_partition));
    } else if (current_partition->size() == 1){
      std::cout << "Trivial partition (terms size = 1): " << partition_count << "\n";
      mainSolver->push((*current_partition)[0]);
    } else {
      std::cout << "Empty partition (terms size = 0): " << partition_count << "\n";
      mainSolver->push(logic->mkConst(logic->getSort_bool(), Logic::tk_true));
      // GF: adding (assert true) for debugging only
    }
  }
  current_partition = NULL;
}

