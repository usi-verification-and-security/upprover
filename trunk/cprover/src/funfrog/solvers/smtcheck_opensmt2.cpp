/*******************************************************************\

Module: Wrapper for OpenSMT2. Based on satcheck_minisat.

Author: Grigory Fedyukovich

\*******************************************************************/

#include "smtcheck_opensmt2.h"

//#define SMT_DEBUG
#define DEBUG_SSA_SMT

void smtcheck_opensmt2t::initializeSolver()
{
  osmt = new Opensmt(opensmt_logic::qf_lra); // GF: hardcode for now
  //logic = &(osmt->getLogic());
  logic = &(osmt->getLRALogic());
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

literalt smtcheck_opensmt2t::const_var(bool val)
{
  literalt l = new_variable();
  PTRef c = var ? logic->getTerm_true() : logic->getTerm_false();
  literals.push_back (c);
  return l;
}

literalt smtcheck_opensmt2t::convert(const exprt &expr)
{
    if(converted_exprs.find(expr.full_hash()) != converted_exprs.end())
        return converted_exprs[expr.full_hash()];

#ifdef SMT_DEBUG
    cout << "; CONVERTING " << expr.pretty() << endl;
#endif
	literalt l;
	if(expr.id()==ID_symbol || expr.id()==ID_nondet_symbol){
#ifdef SMT_DEBUG
        cout << "; IT IS A VAR" << endl;
#endif
		//string str = id2string(to_symbol_expr(expr).get_identifier());
        string str = id2string(expr.get(ID_identifier));

        if(expr.id() == ID_nondet_symbol && str.find("nondet") == std::string::npos)
			str = str.replace(0,7, "symex::nondet");

        string toremove[] = {"!", "::", "|", "\\", "#", "_"};
        string newstr("");
        for(int i = 0; i < str.size(); ++i)
        {
            char c = str[i];
            if(c == '!' || c == ':' || c == '|' || c == '\\' || c == '#' || c == '_')
                continue;
            newstr += c;
        }
        str = newstr;

        PTRef var;
        //typecheck
        if(is_number(expr.type()))
            var = logic->mkRealVar(str.c_str());
        else
            var = logic->mkBoolVar(str.c_str());

		l = new_variable();
		literals.push_back (var);
	} else if (expr.id()==ID_constant) {
#ifdef SMT_DEBUG
        cout << "; IT IS A CONSTANT --" << expr.print_number_2smt() << "--ORIG-EXPR " << expr.get(ID_value) << " :: " << expr.type().id() << endl;
#endif
		if (expr.is_boolean()) {
			l = const_var(expr.is_true());
		} else {
			std::string const_val = expr.print_number_2smt(); // cprover - util code works only for positive or unsigned!
			// If can be that we missed more cases... use the debug prints to check conversions!!

            PTRef rconst = logic->mkConst(const_val.c_str()); // Can have a wrong conversion sometimes!
            l = new_variable();
            literals.push_back(rconst);

            // Check the conversion from string to real was done properly - do not erase!
            assert(!logic->isRealOne(rconst) || expr.is_one()); // Check the conversion works: One => one
            assert(!logic->isRealZero(rconst) || expr.is_zero()); // Check the conversion works: Zero => zero
            // If there is a problem usually will fails on Zero => zero since space usually translated into zero :-)
		}
	} else if (expr.id() == ID_typecast && expr.has_operands()) {
#ifdef SMT_DEBUG
        cout << "; IT IS A TYPECAST" << endl;
#endif
		// KE: Take care of type cast: two cases (1) const and (2) val (var in SMT)
		// First try to code it (just replace the binary to real and val/var just create without time cast
        PTRef ptl;
        l = new_variable();
		if ((expr.operands())[0].is_constant()) {
			ptl = logic->mkConst(expr.get(ID_C_cformat).c_str());
		} else {
			// GF: sometimes typecast is applied to variables, e.g.:
			//     (not (= (typecast |c::main::1::c!0#4|) -2147483648))
			//     in this case, we should replace it by the variable itself, i.e.:
			//     (not (= |c::main::1::c!0#4| -2147483648))
			ptl = logic->mkRealVar(id2string(expr.get(ID_identifier)).c_str());
		}
		literals.push_back(ptl);
	} else {
#ifdef SMT_DEBUG
        cout << "; IT IS AN OPERATOR" << endl;
#endif

#ifdef SMT_DEBUG
        if (expr.has_operands() && expr.operands().size() > 1) {
        	if ((expr.operands()[0] == expr.operands()[1]) &&
        		  ((expr.id() == ID_mult) ||
        		   (expr.id() == ID_floatbv_mult))
        	){
        		cout << "; IT IS AN OPERATOR BETWEEN SAME EXPR: NOT SUPPORTED FOR NONDET" << endl;
        		assert(false);
			}
		}
#endif
        // Check if for div op there is a rounding variable
        bool is_div_wtrounding = false;
        if (expr.id() == ID_floatbv_div || expr.id() == ID_div) {
        	if ((expr.operands()).size() > 2)
        		is_div_wtrounding = true; // need to take care differently!
        }
        // End of check - shall be on a procedure!

        vec<PTRef> args;
        int i = 0;
        forall_operands(it, expr)
        {	// KE: recursion in case the expr is not simple - shall be in a visitor
			if (is_div_wtrounding && i >= 2) { // Divide with 3 operators
				// Skip - we don't need the rounding variable for non-bv logics
			} else { // All the rest of the operators
				literalt cl = convert(*it);
				PTRef cp = literals[cl.var_no()];
				assert(cp != PTRef_Undef);
				args.push(cp);
			}
			i++;
		}

        l = new_variable();
        PTRef ptl;
		if (expr.id()==ID_notequal) {
            ptl = logic->mkNot(logic->mkEq(args));
		} /*else if (expr.id()==ID_if) {
            ptl = logic->mkImpl(args);
		} */else if(expr.id() == ID_ifthenelse) {
            ptl = logic->mkIte(args);
		} else if(expr.id() == ID_and) {
            ptl = logic->mkAnd(args);
		} else if(expr.id() == ID_or) {
            ptl = logic->mkOr(args);
		} else if(expr.id() == ID_not) {
            ptl = logic->mkNot(args);
		} else if(expr.id() == ID_implies) {
            ptl = logic->mkImpl(args);
        } else if(expr.id() == ID_ge) {
            ptl = logic->mkRealGeq(args);
		} else if(expr.id() == ID_le) {
            ptl = logic->mkRealLeq(args);
		} else if(expr.id() == ID_gt) {
            ptl = logic->mkRealGt(args);
		} else if(expr.id() == ID_lt) {
            ptl = logic->mkRealLt(args);
		} else if(expr.id() == ID_plus) {
            ptl = logic->mkRealPlus(args);
		} else if(expr.id() == ID_minus) {
            ptl = logic->mkRealMinus(args);
		} else if(expr.id() == ID_unary_minus) {
            ptl = logic->mkRealMinus(args);
		} else if(expr.id() == ID_unary_plus) {
            ptl = logic->mkRealPlus(args);
		} else if(expr.id() == ID_mult) {
            ptl = logic->mkRealTimes(args);
		} else if(expr.id() == ID_div) {
            ptl = logic->mkRealDiv(args);
		} else if(expr.id() == ID_assign) {
            ptl = logic->mkEq(args);
        } else if(expr.id() == ID_equal) {
            ptl = logic->mkEq(args);
		} else if(expr.id() == ID_floatbv_plus) {
            ptl = logic->mkRealPlus(args);
		} else if(expr.id() == ID_floatbv_minus) {
            ptl = logic->mkRealMinus(args);
		} else if(expr.id() == ID_floatbv_div) {
			ptl = logic->mkRealDiv(args);
		} else if(expr.id() == ID_floatbv_mult) {
			ptl = logic->mkRealTimes(args);
		} else {
#ifdef DEBUG_SSA_SMT // KE - Remove assert if you wish to have debug info
            cout << expr.id() << ";Don't really know how to deal with this operation:\n" << expr.pretty() << endl;
#else
            cout << ";Don't really know how to deal with this operation:\n" << expr.pretty() << endl;
            assert(false);
#endif
            // KE: Missing float op: ID_floatbv_sin, ID_floatbv_cos
            // Do we need them now?
        }
        literals.push_back(ptl);
	}
    converted_exprs[expr.full_hash()] = l;
    PTRef ptr = literals[l.var_no()];
#ifdef SMT_DEBUG
    cout << "; Created OpenSMT2 formula " << logic->printTerm(ptr) << endl;
#endif
    return l;
}

void smtcheck_opensmt2t::set_to_true(const exprt &expr)
{
    literalt l = convert(expr);
    PTRef lp = literals[l.var_no()];
    PTRef truep = logic->getTerm_true();
    vec<PTRef> args;
    args.push(lp);
    args.push(truep);
    PTRef tlp = logic->mkEq(args);

    assert(tlp != PTRef_Undef);
	current_partition->push(tlp);
}

void smtcheck_opensmt2t::set_equal(literalt l1, literalt l2){
    vec<PTRef> args;
    PTRef pl1 = literals[l1.var_no()];
    PTRef pl2 = literals[l2.var_no()];
    args.push(pl1);
    args.push(pl2);
    PTRef ans = logic->mkEq(args);
    literalt l = new_variable();
    literals.push_back(ans);

    assert(ans != PTRef_Undef);
	current_partition->push(ans);
}

literalt smtcheck_opensmt2t::limplies(literalt l1, literalt l2){
	literalt l;
    vec<PTRef> args;
    PTRef pl1 = literals[l1.var_no()];
    PTRef pl2 = literals[l2.var_no()];
    args.push(pl1);
    args.push(pl2);
    PTRef ans = logic->mkImpl(args);
    l = new_variable();
    literals.push_back(ans);
	return l;
}

literalt smtcheck_opensmt2t::land(literalt l1, literalt l2){
	literalt l;
    vec<PTRef> args;
    PTRef pl1 = literals[l1.var_no()];
    PTRef pl2 = literals[l2.var_no()];
    args.push(pl1);
    args.push(pl2);
    PTRef ans = logic->mkAnd(args);
    l = new_variable();
    literals.push_back(ans);
	return l;
}

literalt smtcheck_opensmt2t::land(bvt b){
    literalt l;
    vec<PTRef> args;
    for(bvt::iterator it = b.begin(); it != b.end(); ++it)
    {
        PTRef tmpp = literals[it->var_no()];
        args.push(tmpp);
    }
    PTRef ans = logic->mkAnd(args);
    l = new_variable();
    literals.push_back(ans);
	return l;
}

literalt smtcheck_opensmt2t::lor(literalt l1, literalt l2){
	literalt l;
    vec<PTRef> args;
    PTRef pl1 = literals[l1.var_no()];
    PTRef pl2 = literals[l2.var_no()];
    args.push(pl1);
    args.push(pl2);
    PTRef ans = logic->mkOr(args);
    l = new_variable();
    literals.push_back(ans);
	return l;
}

literalt smtcheck_opensmt2t::lor(bvt b){
    literalt l;
    vec<PTRef> args;
    for(bvt::iterator it = b.begin(); it != b.end(); ++it)
    {
        PTRef tmpp = literals[it->var_no()];
        args.push(tmpp);
    }
    PTRef ans = logic->mkOr(args);
    l = new_variable();
    literals.push_back(ans);
	return l;
}

literalt smtcheck_opensmt2t::lnot(literalt l){
    literalt ln;
    vec<PTRef> args;
    PTRef pl1 = literals[l.var_no()];
    args.push(pl1);
    PTRef ans = logic->mkNot(args);
    ln = new_variable();
    literals.push_back(ans);
	return ln;
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
    //mainSolver->writeSolverState_smtlib2("__SMT_query", &msg1);
  }

  ready_to_interpolate = false;

  if (current_partition != NULL) {
    close_partition();
  }

//  add_variables();
  char *msg;
  for(int i = 0; i < top_level_formulas.size(); ++i)
      mainSolver->insertFormula(top_level_formulas[i], &msg);
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
      PTRef pand = logic->mkAnd(*current_partition);
      //cout << "; Pushing to solver: " << logic->printTerm(pand) << endl;
      //mainSolver->push(pand);
      top_level_formulas.push(pand);
    } else if (current_partition->size() == 1){
      PTRef pand = (*current_partition)[0];
      //cout << "; Pushing to solver: " << logic->printTerm(pand) << endl;
      std::cout << "Trivial partition (terms size = 1): " << partition_count << "\n";
      //mainSolver->push(pand);
      top_level_formulas.push(pand);
    } else {
      std::cout << "Empty partition (terms size = 0): " << partition_count << "\n";
      //mainSolver->push(logic->getTerm_true());
      top_level_formulas.push(logic->getTerm_true());
      // GF: adding (assert true) for debugging only
    }
  }
  current_partition = NULL;
}

