/*******************************************************************\

Module: Wrapper for OpenSMT2. Based on satcheck_minisat.

Author: Grigory Fedyukovich

\*******************************************************************/
#include "smtcheck_opensmt2_lra.h"

//#define SMT_DEBUG

void smtcheck_opensmt2t_lra::initializeSolver()
{
  osmt = new Opensmt(opensmt_logic::qf_lra);
  lralogic = &(osmt->getLRALogic());
  logic = &(osmt->getLogic());
  mainSolver = &(osmt->getMainSolver());
  const char* msg;
  osmt->getConfig().setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);

  // KE: Fix a strange bug can be related to the fact we are pushing
  // a struct into std::vector and use [] before any push_back
  literals.push_back(PTRef());
  literalt l = new_variable(); // Shall be location 0, i.e., [l.var_no()] is [0]
  literals[0] = logic->getTerm_true(); // Which is .x =0
  // KE: End of fix
}

// Free all inner objects
smtcheck_opensmt2t_lra::~smtcheck_opensmt2t_lra()
{
	// Shall/When need to: freeSolver() ?
}

literalt smtcheck_opensmt2t_lra::const_var_Real(const exprt &expr)
{
	literalt l;
	PTRef rconst = lralogic->mkConst(extract_expr_str_number(expr).c_str()); // Can have a wrong conversion sometimes!

	// Check the conversion from string to real was done properly - do not erase!
	assert(!lralogic->isRealOne(rconst) || expr.is_one()); // Check the conversion works: One => one
    if(expr.is_constant() && !expr.is_boolean()) {
    	assert(!lralogic->isRealZero(rconst) || (expr.is_zero())); // If fails here for zero, check if also the negation is not zero
    } else {
    	exprt temp_check = exprt(expr); temp_check.negate();
		assert(!lralogic->isRealZero(rconst) || (expr.is_zero() || temp_check.is_zero())); // Check the conversion works: Zero => zero
		// If there is a problem usually will fails on Zero => zero since space usually translated into zero :-)
    }

	l = push_variable(rconst); // Keeps the new PTRef + create for it a new index/literal

	return l;
}

literalt smtcheck_opensmt2t_lra::type_cast(const exprt &expr) {
	literalt l;

	// KE: Take care of type cast - recursion of convert take care of it anyhow
    // Unless it is constant bool, that needs different code:
    if (expr.is_boolean() && (expr.operands())[0].is_constant()) {
    	std::string val = extract_expr_str_number((expr.operands())[0]);
    	bool val_const_zero = (val.size()==0) || (stod(val)==0.0);
    	l = const_var(!val_const_zero);
    } else if (!expr.is_boolean() && (expr.operands())[0].is_boolean()) {
    	// Cast from Boolean to Real - Add
    	literalt lt = convert((expr.operands())[0]); // Creating the Bool expression
    	PTRef ptl = lralogic->mkIte(literals[lt.var_no()], lralogic->mkConst("1"), lralogic->mkConst("0"));
    	l = push_variable(ptl); // Keeps the new literal + index it
	} else {
    	l = convert((expr.operands())[0]);
    }

#ifdef SMT_DEBUG
    char* s = getPTermString(l);
    cout << "; (TYPE_CAST) For " << expr.id() << " Created OpenSMT2 formula " << s << endl;
    free(s);
#endif

    return l;
}

literalt smtcheck_opensmt2t_lra::convert(const exprt &expr)
{
// GF: disabling hash for a while, since it leads to bugs at some particular cases,
//     e.g., for (= |goto_symex::guard#3| (< |c::f::a!0#7| 10))
//           and (= |goto_symex::guard#4| (< |c::f::a!0#11| 10))
//
//    if(converted_exprs.find(expr.hash()) != converted_exprs.end())
//        return converted_exprs[expr.hash()];

#ifdef SMT_DEBUG
    cout << "; ON PARTITION " << partition_count << " CONVERTING with " << expr.has_operands() << " operands "<< endl;
#endif

    /* Check which case it is */
	literalt l;
	if(expr.id()==ID_symbol || expr.id()==ID_nondet_symbol){
#ifdef SMT_DEBUG
        cout << "; IT IS A VAR" << endl;
#endif
        l = lvar(expr);
	} else if (expr.id()==ID_constant) {
#ifdef SMT_DEBUG
        cout << "; IT IS A CONSTANT " << endl;
#endif
        l = lconst(expr);
	} else if (expr.id() == ID_typecast && expr.has_operands()) {
#ifdef SMT_DEBUG
		bool is_const =(expr.operands())[0].is_constant(); // Will fail for assert(0) if code changed here not carefully!
        cout << "; IT IS A TYPECAST OF " << (is_const? "CONST " : "") << expr.type().id() << endl;
#endif
		// KE: Take care of type cast - recursion of convert take care of it anyhow
        // Unless it is constant bool, that needs different code:
        l = type_cast(expr);
	} else if (expr.id() == ID_typecast) {
#ifdef SMT_DEBUG
		cout << "EXIT WITH ERROR: operator does not yet supported in the LRA version (token: " << expr.id() << ")" << endl;
		assert(false); // Need to take care of - typecast no operands
#else
		l = lunsupported2var(expr);
#endif
	} else {
#ifdef SMT_DEBUG
        cout << "; IT IS AN OPERATOR" << endl;

        if (expr.has_operands() && expr.operands().size() > 1) {
        	if ((expr.operands()[0] == expr.operands()[1]) &&
        		(!expr.operands()[1].is_constant())	&&
        		  ((expr.id() == ID_div) ||
        		   (expr.id() == ID_floatbv_div) ||
        	       (expr.id() == ID_mult) ||
        		   (expr.id() == ID_floatbv_mult))
        	){
        		cout << "; IT IS AN OPERATOR BETWEEN SAME EXPR: NOT SUPPORTED FOR NONDET" << endl;
        		assert(false);
			}
		}
#endif
        // Check if for div op there is a rounding variable
        bool is_div_wtrounding = // need to take care differently!
        		((expr.id() == ID_floatbv_minus || expr.id() == ID_minus ||
        		  expr.id() == ID_floatbv_plus || expr.id() == ID_plus ||
    		      expr.id() == ID_floatbv_div || expr.id() == ID_div ||
    		      expr.id() == ID_floatbv_mult || expr.id() == ID_mult)
    		    &&
    		    ((expr.operands()).size() > 2));

        vec<PTRef> args;
        int i = 0;
        bool is_no_support = false;
        forall_operands(it, expr)
        {	// KE: recursion in case the expr is not simple - shall be in a visitor
        	bool is_builtin_rounding_mode =
        			(id2string(it->get(ID_identifier)).find("__CPROVER_rounding_mode#")!=std::string::npos);
			if ((is_div_wtrounding && i >= 2) || is_builtin_rounding_mode)
			{
				// Skip - we don't need the rounding variable for non-bv logics + assure it is always rounding thing
				if (!is_builtin_rounding_mode) {
#ifdef SMT_DEBUG
					cout << "EXIT WITH ERROR: * and / operators with more than 2 arguments have no support yet in the LRA version (token: "
							<< expr.id() << ")" << endl;
					assert(false); // No support yet for more than two arguments for these operators
#else
					is_no_support = true; // Will cause to over approx all
#endif
				}
			}
			else
			{ // All the rest of the operators
				literalt cl = convert(*it);
				PTRef cp = literals[cl.var_no()];
				assert(cp != PTRef_Undef);
	 			args.push(cp);
#ifdef SMT_DEBUG
	 			char *s = lralogic->printTerm(cp);
				cout << "; On inner iteration " << i
						<< " Op to command is var no " << cl.var_no()
						<< " inner index " << cp.x
						<< " with hash code " << (*it).full_hash()
						<< " and the other one " << (*it).hash()
						<< " in address " << (void *)&(*it)
						<< " of term " << s
						<< " from |" << (*it).get(ID_identifier)
						<< "| these should be the same !" << endl; // Monitor errors in the table!

				// Auto catch this kind if problem and throws and assert!
				if((*it).id()==ID_symbol || (*it).id()==ID_nondet_symbol){
					std::stringstream convert, convert2; // stringstream used for the conversion
					convert << s; std::string str_expr1 = convert.str();
					convert2 << "|" << (*it).get(ID_identifier) << "|"; std::string str_expr2 = convert2.str();
					str_expr2.erase(std::remove(str_expr2.begin(),str_expr2.end(),'\\'),str_expr2.end());
					if((*it).id() == ID_nondet_symbol && str_expr2.find("nondet") == std::string::npos)
						str_expr2 = str_expr2.replace(1,7, "symex::nondet");
					assert(str_expr1.compare(str_expr2) == 0);
				}
				free(s);
#endif
				i++; // Only if really add an item to mult/div inc the counter
			}
		}

        PTRef ptl;
        if (is_no_support) { // If we don't supposrt the operator due to more than 2 args
        	ptl = literals[lunsupported2var(expr).var_no()];
        } else if (expr.id()==ID_notequal) {
            ptl = lralogic->mkNot(lralogic->mkEq(args));
        } else if(expr.id() == ID_equal) {
            ptl = lralogic->mkEq(args);
		} else if (expr.id()==ID_if) {
            ptl = lralogic->mkIte(args);
#ifdef DEBUG_SMT2SOLVER
            ite_map_str.insert(make_pair(string(getPTermString(ptl)),lralogic->printTerm(lralogic->getTopLevelIte(ptl))));
#endif
		} else if(expr.id() == ID_ifthenelse) {
            ptl = lralogic->mkIte(args);
#ifdef DEBUG_SMT2SOLVER
            ite_map_str.insert(make_pair(string(getPTermString(ptl)),lralogic->printTerm(lralogic->getTopLevelIte(ptl))));
#endif
		} else if(expr.id() == ID_and) {
            ptl = lralogic->mkAnd(args);
		} else if(expr.id() == ID_or) {
            ptl = lralogic->mkOr(args);
		} else if(expr.id() == ID_not) {
            ptl = lralogic->mkNot(args);
		} else if(expr.id() == ID_implies) {
            ptl = lralogic->mkImpl(args);
        } else if(expr.id() == ID_ge) {
            ptl = lralogic->mkRealGeq(args);
		} else if(expr.id() == ID_le) {
            ptl = lralogic->mkRealLeq(args);
		} else if(expr.id() == ID_gt) {
            ptl = lralogic->mkRealGt(args);
		} else if(expr.id() == ID_lt) {
            ptl = lralogic->mkRealLt(args);
		} else if(expr.id() == ID_plus) {
            ptl = lralogic->mkRealPlus(args);
		} else if(expr.id() == ID_minus) {
            ptl = lralogic->mkRealMinus(args);
		} else if(expr.id() == ID_unary_minus) {
            ptl = lralogic->mkRealMinus(args);
		} else if(expr.id() == ID_unary_plus) {
            ptl = lralogic->mkRealPlus(args);
		} else if(expr.id() == ID_mult) {
#ifdef SMT_DEBUG
			assert(isLinearOp(expr,args));
			ptl = lralogic->mkRealTimes(args);
#else
			if (isLinearOp(expr,args))
				ptl = lralogic->mkRealTimes(args);
			else
				ptl = literals[lunsupported2var(expr).var_no()];
#endif
		} else if(expr.id() == ID_div) {
#ifdef SMT_DEBUG
			assert(isLinearOp(expr,args));
			ptl = lralogic->mkRealDiv(args);
#else
			if (isLinearOp(expr,args))
				ptl = lralogic->mkRealDiv(args);
			else
				ptl = literals[lunsupported2var(expr).var_no()];
#endif
		} else if(expr.id() == ID_assign) {
            ptl = lralogic->mkEq(args);
        } else if(expr.id() == ID_ieee_float_equal) {
            ptl = lralogic->mkEq(args);
        } else if(expr.id() == ID_ieee_float_notequal) {
            ptl = lralogic->mkNot(lralogic->mkEq(args));
		} else if(expr.id() == ID_floatbv_plus) {
            ptl = lralogic->mkRealPlus(args);
		} else if(expr.id() == ID_floatbv_minus) {
            ptl = lralogic->mkRealMinus(args);
		} else if(expr.id() == ID_floatbv_div) {
#ifdef SMT_DEBUG
			assert(isLinearOp(expr,args));
			ptl = lralogic->mkRealDiv(args);
#else
			if (isLinearOp(expr,args))
				ptl = lralogic->mkRealDiv(args);
			else
				ptl = literals[lunsupported2var(expr).var_no()];
#endif
		} else if(expr.id() == ID_floatbv_mult) {
#ifdef SMT_DEBUG
			assert(isLinearOp(expr,args));
			ptl = lralogic->mkRealTimes(args);
#else
			if (isLinearOp(expr,args))
				ptl = lralogic->mkRealTimes(args);
			else
				ptl = literals[lunsupported2var(expr).var_no()];
#endif

		} else if(expr.id() == ID_index) {
#ifdef SMT_DEBUG
			cout << "EXIT WITH ERROR: Arrays and index of an array operator have no support yet in the LRA version (token: "
					<< expr.id() << ")" << endl;
			assert(false); // No support yet for arrays
#else
			ptl = literals[lunsupported2var(expr).var_no()];
#endif
		} else {
#ifdef SMT_DEBUG // KE - Remove assert if you wish to have debug info
            cout << expr.id() << ";Don't really know how to deal with this operation:\n" << expr.pretty() << endl;
            cout << "EXIT WITH ERROR: operator does not yet supported in the LRA version (token: "
            		<< expr.id() << ")" << endl;
            assert(false);
#else
            ptl = literals[lunsupported2var(expr).var_no()];
#endif
            // KE: Missing float op: ID_floatbv_sin, ID_floatbv_cos
            // Do we need them now?
        }
		l = push_variable(ptl); // Keeps the new PTRef + create for it a new index/literal
	}
    converted_exprs[expr.hash()] = l;
#ifdef SMT_DEBUG
    PTRef ptr = literals[l.var_no()];
    char *s = lralogic->printTerm(ptr);
    cout << "; For " << expr.id() << " Created OpenSMT2 formula " << s << endl;
    free(s);
#endif
    return l;
}

literalt smtcheck_opensmt2t_lra::lunsupported2var(exprt expr)
{
	literalt l;
	PTRef var;

	const string str =  "funfrog::c::unsupported_op2var#" + std::to_string(unsupported2var++);
	if (expr.is_boolean())
		var = lralogic->mkBoolVar(str.c_str());
	else
		var = lralogic->mkRealVar(str.c_str());

	l = push_variable(var);

	return l;
}

literalt smtcheck_opensmt2t_lra::lvar(const exprt &expr)
{
	const string _str = extract_expr_str_name(expr); // NOTE: any changes to name - please added it to general method!
    string str = remove_invalid(_str);
    str = quote_varname(str);

    // Nil is a special case - don't create a var but a val of true
    if (_str.compare("nil") == 0) return const_var(true);

#ifdef SMT_DEBUG
	cout << "; (lvar) Create " << str << endl;
#endif

    // Else if it is really a var, continue and declare it!
	literalt l;
    PTRef var;
    if(is_number(expr.type()))
    	var = lralogic->mkRealVar(str.c_str());
    else if (expr.type().id() == ID_array) { // Is a function with index
#ifdef SMT_DEBUG
    	cout << "EXIT WITH ERROR: Arrays and index of an array operator have no support yet in the LRA version (token: "
    			<< expr.type().id() << ")" << endl;
    	assert(false); // No support yet for arrays
#else
    	var = literals[lunsupported2var(expr).var_no()];
#endif
    } else
    	var = lralogic->mkBoolVar(str.c_str());

    l = push_variable(var); // Keeps the new PTRef + create for it a new index/literal

#ifdef DEBUG_SMT2SOLVER
	std::string add_var = str + " () " + getVarData(var);
	if (var_set_str.end() == var_set_str.find(add_var)) {
		var_set_str.insert(add_var);
	}
#endif

	return l;
}

literalt smtcheck_opensmt2t_lra::lconst(const exprt &expr)
{
	literalt l;
	if (expr.is_boolean()) {
		l = const_var(expr.is_true());
	} else {
		l = const_var_Real(expr);
	}

	return l;
}

/*******************************************************************\

Function: smtcheck_opensmt2t::isLinearOp

  Inputs: expression of * or /

 Outputs: true if linear op else false

 Purpose: we cannot express x*x or nodet*nodet (any) in LRA - assure
          we are not trying to push such an expression to the solver
          In case we sent this to the solver we will get assertion
          violation!

\*******************************************************************/
bool smtcheck_opensmt2t_lra::isLinearOp(const exprt &expr, vec<PTRef> &args) {
	// Must be true
	if (!expr.has_operands()) return true;
	if (expr.operands().size() < 2) return true;
	if (expr.operands()[0].is_constant()) return true;
	if (expr.operands()[1].is_constant()) return true;

	// Must be false if there is more than one var
	int count_var = 0;
	for (int i=0; i< args.size(); i++) {
		count_var += lralogic->isRealVar(args[i]) ? 1 : 0;
	}
	if (count_var > 1) {
#ifdef SMT_DEBUG
		cout << "EXIT WITH ERROR: Using Unbounded mul/div operator" << endl;
#endif
		return false; // e.g. when a*b is the instruction
	}


	// Don't know
	return true; // Probably missed cased of false, so once found please add it
}

/*******************************************************************\

Function: smtcheck_opensmt2t_lra::extract_expr_str_name

  Inputs: expression that is a var

 Outputs: a string of the name

 Purpose: assure we are extracting the name correctly and in one place.

\*******************************************************************/
std::string smtcheck_opensmt2t_lra::extract_expr_str_name(const exprt &expr)
{
	string str = id2string(expr.get(ID_identifier));
	assert (str.size() != 0); // Check the we really got something

	if(expr.id() == ID_nondet_symbol && str.find("nondet") == std::string::npos)
		str = str.replace(0,7, "symex::nondet");

	if (str.find("__CPROVER_rounding_mode#") != std::string::npos) {
	#ifdef DEBUG_SSA_SMT // KE - Remove assert if you wish to have debug info
		cout << "; " << str << " :: " << expr.id() << " - Should Not Add Rounding Model\n" << expr.pretty() << endl;
	#else
        cout << "EXIT WITH ERROR: Using Rounding Model in LRA " << str << endl;  
		assert(false);
	#endif
	}

	return str;
}


