/*******************************************************************\

Module: Wrapper for OpenSMT2. Based on satcheck_minisat.

Author: Grigory Fedyukovich

\*******************************************************************/
#include <queue>

#include "smtcheck_opensmt2.h"

//#define SMT_DEBUG
//#define DEBUG_SSA_SMT
//#define DEBUG_SSA_SMT_NUMERIC_CONV
//#define DEBUG_SMT_EUF

const char* smtcheck_opensmt2t::tk_sort_ureal = "UReal";
const char* smtcheck_opensmt2t::tk_mult = "*";
const char* smtcheck_opensmt2t::tk_div = "/";
const char* smtcheck_opensmt2t::tk_plus = "+";
const char* smtcheck_opensmt2t::tk_minus = "-";
const char* smtcheck_opensmt2t::tk_lt = "<";
const char* smtcheck_opensmt2t::tk_le = "<=";
const char* smtcheck_opensmt2t::tk_gt = ">";
const char* smtcheck_opensmt2t::tk_ge = ">=";

void smtcheck_opensmt2t::initializeSolver()
{
  osmt = new Opensmt(opensmt_logic::qf_uf);
  logic = &(osmt->getLogic());
  mainSolver = &(osmt->getMainSolver());
  const char* msg2;
  osmt->getConfig().setOption(SMTConfig::o_produce_inter, SMTOption(true), msg2);
  //osmt->getConfig().setOption(SMTConfig::o_verbosity, SMTOption(0), msg);

  // KE: Fix a strange bug can be related to the fact we are pushing
  // a struct into std::vector and use [] before any push_back
  literals.push_back(PTRef());
  literalt l = new_variable(); // Shall be location 0, i.e., [l.var_no()] is [0]
  literals[0] = logic->getTerm_true(); // Which is .x =0
  // KE: End of fix

  //Initialize the stuff to fake LRA
  //Create new sort UReal
  IdRef idr = IdRef_Undef;
  idr = logic->newIdentifier(tk_sort_ureal);
  vec<SRef> tmp;
  sort_ureal = logic->newSort(idr, tk_sort_ureal, tmp);
  logic->declare_sort_hook(sort_ureal);

  vec<SRef> args;
  args.push(sort_ureal);
  args.push(sort_ureal);

  char *msg;
  //Declare operations
  s_mult = logic->declareFun(tk_mult, sort_ureal, args, &msg, true);
  s_div = logic->declareFun(tk_div, sort_ureal, args, &msg, true);
  s_plus = logic->declareFun(tk_plus, sort_ureal, args, &msg, true);
  s_minus = logic->declareFun(tk_minus, sort_ureal, args, &msg, true);

  Symbol& smult = logic->getSym(s_mult);
  Symbol& sdiv = logic->getSym(s_div);
  Symbol& splus = logic->getSym(s_plus);
  Symbol& sminus = logic->getSym(s_minus);

  smult.setLeftAssoc();
  sdiv.setLeftAssoc();
  splus.setLeftAssoc();
  sminus.setLeftAssoc();
  smult.setCommutes();
  sdiv.setCommutes();
  splus.setCommutes();
  sminus.setCommutes();
  
  //Declare relations
  s_lt = logic->declareFun(tk_lt, logic->getSort_bool(), args, &msg, true);
  s_le = logic->declareFun(tk_le, logic->getSort_bool(), args, &msg, true);
  s_gt = logic->declareFun(tk_gt, logic->getSort_bool(), args, &msg, true);
  s_ge = logic->declareFun(tk_ge, logic->getSort_bool(), args, &msg, true);

}

PTRef
smtcheck_opensmt2t::mkURealMult(vec<PTRef>& args)
{
    char *msg;
    return logic->mkFun(s_mult, args, &msg);
}
PTRef
smtcheck_opensmt2t::mkURealDiv(vec<PTRef>& args)
{
    char *msg;
    return logic->mkFun(s_div, args, &msg);
}

PTRef
smtcheck_opensmt2t::mkURealPlus(vec<PTRef>& args)
{
    char *msg;
    return logic->mkFun(s_plus, args, &msg);
}

PTRef
smtcheck_opensmt2t::mkURealMinus(vec<PTRef>& args)
{
    char *msg;
    return logic->mkFun(s_minus, args, &msg);
}

PTRef
smtcheck_opensmt2t::mkURealLt(vec<PTRef>& args)
{
    assert(args.size() == 2);
    char *msg;
    return logic->mkFun(s_lt, args, &msg);
}
    
PTRef
smtcheck_opensmt2t::mkURealLe(vec<PTRef>& args)
{
    assert(args.size() == 2);
    char *msg;
    return logic->mkFun(s_le, args, &msg);
}

PTRef
smtcheck_opensmt2t::mkURealGt(vec<PTRef>& args)
{
    assert(args.size() == 2);
    char *msg;
    return logic->mkFun(s_gt, args, &msg);
}
    
PTRef
smtcheck_opensmt2t::mkURealGe(vec<PTRef>& args)
{
    assert(args.size() == 2);
    char *msg;
    return logic->mkFun(s_ge, args, &msg);
}

// Free all resources related to OpenSMT2
void smtcheck_opensmt2t::freeSolver()
{
  if (osmt != NULL) delete osmt;
}

// Free all inner objects
smtcheck_opensmt2t::~smtcheck_opensmt2t()
{


	// Shall/When need to: freeSolver() ?
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

/*******************************************************************\

Function: smtcheck_opensmt2t::push_variable

  Inputs: PTRef to store

 Outputs: Literal that has the index of the stored PTRef in literals

 Purpose: To check if the store of PTRef in literals is sound
 That is given a literal we will always get the original PTRef
 (or error index) - but no other PTRefs...

 NOTE: IN CASE YOU HAVE AN ASSERTION VIOLATION FROM THIS CODE
 	 	 D O   N O T   C O M M E N T   THE DEBUG PRINTS
 	 	 IT SAYS THAT THE MAPPING OF LITERALS TO PTREFS
 	 	 ARE NOT WORKING!! FIX IT, PLEASE
 	 	 REASON: PTREF IS A STRUCT AND VECTOR AND STRUCTS
 	 	 HAVE SOME ISSUES...

\*******************************************************************/
literalt smtcheck_opensmt2t::push_variable(PTRef ptl) {
	literalt l = new_variable();
#ifdef SMT_DEBUG
	// If this assert fails try to check location 0,1 and the rest of the data in literals
	assert(l.var_no() == literals.size());
#endif
	literals.push_back(ptl); // Keeps the new literal + index it
#ifdef SMT_DEBUG
	// THE MAPPING IS WRONG. YOU ARE NOT GETTING THE CORRECT PTREF!!
	assert(ptl.x == (literals[l.var_no()]).x);
#endif
	return l; // Return the literal after creating all ok - check if here with SMT_DEBUG flag
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

// For using symbol only when creating the interpolant (in smt_itpt::substitute)
PTRef smtcheck_opensmt2t::convert_symbol(const exprt &expr)
{
	// Assert if not symbol_exprt
	assert(expr.id()==ID_symbol || expr.id()==ID_nondet_symbol);

	// If it is a symbol create the PTRef for it and returns it
	literalt l = convert(expr);
	return literals[l.var_no()];
}

literalt smtcheck_opensmt2t::const_var_Real(const exprt &expr)
{
    //TODO: Check this
	literalt l;
    string num = "const" + extract_expr_str_number(expr);
	//PTRef rconst = logic->mkVar(sort_ureal, extract_expr_str_number(expr).c_str()); // Can have a wrong conversion sometimes!
	PTRef rconst = logic->mkVar(sort_ureal, num.c_str()); // Can have a wrong conversion sometimes!

	l = push_variable(rconst); // Keeps the new PTRef + create for it a new index/literal

	return l;
}

literalt smtcheck_opensmt2t::const_var(bool val)
{
	literalt l;

	PTRef c = val ? logic->getTerm_true() : logic->getTerm_false();
	l = push_variable(c); // Keeps the new PTRef + create for it a new index/literal

	return l;
}

literalt smtcheck_opensmt2t::type_cast(const exprt &expr) {
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
    	//PTRef ptl = lralogic->mkIte(literals[lt.var_no()], lralogic->mkConst("1"), lralogic->mkConst("0"));
        PTRef ptl = logic->mkIte(literals[lt.var_no()], logic->mkVar(sort_ureal, "1"), logic->mkVar(sort_ureal, "0"));
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
literalt smtcheck_opensmt2t::convert(const exprt &expr)
{
// GF: disabling hash for a while, since it leads to bugs at some particular cases,
//     e.g., for (= |goto_symex::guard#3| (< |c::f::a!0#7| 10))
//           and (= |goto_symex::guard#4| (< |c::f::a!0#11| 10))
//
//    if(converted_exprs.find(expr.hash()) != converted_exprs.end())
//        return converted_exprs[expr.hash()];

#ifdef SMT_DEBUG
    cout << "; ON PARTITION " << partition_count << " CONVERTING with " << expr.has_operands() << " operands "<< /*expr.pretty() << */ endl;
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
		cout << "EXIT WITH ERROR: operator does not yet supported in the QF_UF version (token: " << expr.id() << ")" << endl;
		assert(false); // Need to take care of - typecast no operands
#else
		l = lunsupported2var(expr);
#endif
	} else {
#ifdef SMT_DEBUG
        cout << "; IT IS AN OPERATOR" << endl;
#endif

#ifdef SMT_DEBUG
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
        bool is_div_wtrounding = false;
    	if (expr.id() == ID_floatbv_minus || expr.id() == ID_minus ||
    		expr.id() == ID_floatbv_plus || expr.id() == ID_plus ||
    		expr.id() == ID_floatbv_div || expr.id() == ID_div ||
    		expr.id() == ID_floatbv_mult || expr.id() == ID_mult) {
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
#ifdef DEBUG_SMT_LRA
	 			char *s = logic->printTerm(cp);
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
			}
			i++;
		}

        PTRef ptl;
		if (expr.id()==ID_notequal) {
            ptl = logic->mkNot(logic->mkEq(args));
        } else if(expr.id() == ID_equal) {
            ptl = logic->mkEq(args);
		} else if (expr.id()==ID_if) {
            ptl = logic->mkIte(args);
#ifdef DEBUG_SMT_LRA
            ite_map_str.insert(make_pair(string(getPTermString(ptl)),logic->printTerm(logic->getTopLevelIte(ptl))));
#endif
		} else if(expr.id() == ID_ifthenelse) {
            ptl = logic->mkIte(args);
#ifdef DEBUG_SMT_LRA
            ite_map_str.insert(make_pair(string(getPTermString(ptl)),logic->printTerm(logic->getTopLevelIte(ptl))));
#endif
		} else if(expr.id() == ID_and) {
            ptl = logic->mkAnd(args);
		} else if(expr.id() == ID_or) {
            ptl = logic->mkOr(args);
		} else if(expr.id() == ID_not) {
            ptl = logic->mkNot(args);
		} else if(expr.id() == ID_implies) {
            ptl = logic->mkImpl(args);
        } else if(expr.id() == ID_ge) {
            //ptl = lralogic->mkRealGeq(args);
            ptl = this->mkURealGe(args);
		} else if(expr.id() == ID_le) {
            //ptl = lralogic->mkRealLeq(args);
            ptl = this->mkURealLe(args);
		} else if(expr.id() == ID_gt) {
            //ptl = lralogic->mkRealGt(args);
            ptl = this->mkURealGt(args);
		} else if(expr.id() == ID_lt) {
            //ptl = lralogic->mkRealLt(args);
            ptl = this->mkURealLt(args);
		} else if(expr.id() == ID_plus) {
            //ptl = lralogic->mkRealPlus(args);
            ptl = this->mkURealPlus(args);
		} else if(expr.id() == ID_minus) {
            //ptl = lralogic->mkRealMinus(args);
            ptl = this->mkURealMinus(args);
		} else if(expr.id() == ID_unary_minus) {
            //ptl = lralogic->mkRealMinus(args);
            ptl = this->mkURealMinus(args);
		} else if(expr.id() == ID_unary_plus) {
            //ptl = lralogic->mkRealPlus(args);
            ptl = this->mkURealPlus(args);
		} else if(expr.id() == ID_mult) {
			//ptl = lralogic->mkRealTimes(args);
            ptl = this->mkURealMult(args);
		} else if(expr.id() == ID_div) {
			//ptl = lralogic->mkRealDiv(args);
            ptl = this->mkURealDiv(args);
		} else if(expr.id() == ID_assign) {
            ptl = logic->mkEq(args);
        } else if(expr.id() == ID_ieee_float_equal) {
            ptl = logic->mkEq(args);
        } else if(expr.id() == ID_ieee_float_notequal) {
            ptl = logic->mkNot(logic->mkEq(args));
		} else if(expr.id() == ID_floatbv_plus) {
            //ptl = lralogic->mkRealPlus(args);
            ptl = this->mkURealPlus(args);
		} else if(expr.id() == ID_floatbv_minus) {
            //ptl = lralogic->mkRealMinus(args);
            ptl = this->mkURealMinus(args);
		} else if(expr.id() == ID_floatbv_div) {
			//ptl = lralogic->mkRealDiv(args);
            ptl = this->mkURealDiv(args);
		} else if(expr.id() == ID_floatbv_mult) {
			//ptl = lralogic->mkRealTimes(args);
            ptl = this->mkURealMult(args);
		} else if(expr.id() == ID_index) {
#ifdef SMT_DEBUG
			cout << "EXIT WITH ERROR: Arrays and index of an array operator have no support yet in the LRA version (token: "
					<< expr.id() << ")" << endl;
			assert(false); // No support yet for arrays
#else
			ptl = literals[lunsupported2var(expr).var_no()];
#endif
		} else {
#ifdef DEBUG_SSA_SMT // KE - Remove assert if you wish to have debug info
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
    char *s = logic->printTerm(ptr);
    cout << "; For " << expr.id() << " Created OpenSMT2 formula " << s << endl;
    free(s);
#endif
    return l;
}

literalt smtcheck_opensmt2t::lunsupported2var(exprt expr)
{
	literalt l;
	PTRef var;

	const string str =  "funfrog::c::unsupported_op2var#" + (unsupported2var++);
    var = logic->mkBoolVar(str.c_str());

	l = push_variable(var);

	return l;
}

void smtcheck_opensmt2t::set_to_true(PTRef ptr)
{
	push_variable(ptr); // Keeps the new PTRef + create for it a new index/literal
    assert(ptr != PTRef_Undef);
	current_partition->push(ptr);
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

void smtcheck_opensmt2t::set_to_false(const exprt &expr)
{
    literalt l = convert(expr);
    PTRef lp = literals[l.var_no()];
    PTRef falsep = logic->getTerm_false();
    vec<PTRef> args;
    args.push(lp);
    args.push(falsep);
    PTRef tlp = logic->mkEq(args);

    assert(tlp != PTRef_Undef);
	current_partition->push(tlp);
}

void smtcheck_opensmt2t::set_equal(literalt l1, literalt l2){
    vec<PTRef> args;
    literalt l;
    PTRef pl1 = literals[l1.var_no()];
    PTRef pl2 = literals[l2.var_no()];
    args.push(pl1);
    args.push(pl2);
    PTRef ans = logic->mkEq(args);
    l = push_variable(ans); // Keeps the new PTRef + create for it a new index/literal
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
    l = push_variable(ans); // Keeps the new PTRef + create for it a new index/literal

	return l;
}

literalt smtcheck_opensmt2t::lnotequal(literalt l1, literalt l2){
	literalt l;
    vec<PTRef> args;
    PTRef pl1 = literals[l1.var_no()];
    PTRef pl2 = literals[l2.var_no()];
    args.push(pl1);
    args.push(pl2);
    PTRef ans = logic->mkNot(logic->mkEq(args));
    l = push_variable(ans); // Keeps the new PTRef + create for it a new index/literal

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
    l = push_variable(ans); // Keeps the new PTRef + create for it a new index/literal

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
    l = push_variable(ans); // Keeps the new PTRef + create for it a new index/literal

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
    l = push_variable(ans); // Keeps the new PTRef + create for it a new index/literal

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
    l = push_variable(ans); // Keeps the new PTRef + create for it a new index/literal

	return l;
}

literalt smtcheck_opensmt2t::lnot(literalt l){
    literalt ln;
    vec<PTRef> args;
    PTRef pl1 = literals[l.var_no()];
    args.push(pl1);
    PTRef ans = logic->mkNot(args);
    ln = push_variable(ans); // Keeps the new PTRef + create for it a new index/literal

	return ln;
}

literalt smtcheck_opensmt2t::lvar(const exprt &expr)
{
	const string _str = extract_expr_str_name(expr); // NOTE: any changes to name - please added it to general method!
    string str = remove_invalid(_str);
    str = quote_varname(str);

    // Nil is a special case - don't create a var but a val of true
    if (_str.compare("nil") == 0) return const_var(true);

    // Else if it is really a var, continue and declare it!
	literalt l;
    PTRef var;
    if(is_number(expr.type()))
        //TODO: Check this
    	var = logic->mkVar(sort_ureal, str.c_str());
    else if (expr.type().id() == ID_array) { // Is a function with index
#ifdef SMT_DEBUG
    	cout << "EXIT WITH ERROR: Arrays and index of an array operator have no support yet in the LRA version (token: "
    			<< expr.type().id() << ")" << endl;
    	assert(false); // No support yet for arrays
#else
    	var = literals[lunsupported2var(expr).var_no()];
#endif
    } else
    	var = logic->mkBoolVar(str.c_str());

    l = push_variable(var); // Keeps the new PTRef + create for it a new index/literal

#ifdef DEBUG_SMT_LRA
	cout << "; (lvar) Create " << str << endl;
	std::string add_var = str + " () " + getVarData(var);
	if (var_set_str.end() == var_set_str.find(add_var)) {
		var_set_str.insert(add_var);
	}
#endif

	return l;
}

literalt smtcheck_opensmt2t::lconst(const exprt &expr)
{
	literalt l;
	if (expr.is_boolean()) {
		l = const_var(expr.is_true());
	} else {
        l = const_var_Real(expr);
	}

	return l;
}

void smtcheck_opensmt2t::extract_itp(PTRef ptref, smt_itpt& itp) const
{
  //ptref_cachet cache;
  //  target_itp.set_no_original_variables(no_literals);
  //target_itp.root_literal = extract_itp_rec(ptref, target_itp, cache);

  // KE : interpolant adjustments/remove var indices shall come here
  itp.setInterpolant(ptref);
}

/* KE: Remove code - Will use OpenSMT2 to do so + using only PTref as is
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
      cout << "; error " << logic->getSymName(ptref) << endl;
      assert(ptm.size() == 0);
//      result.set(decode_id(logic->getSymName(ptref)), false);
      //GF: hack
  } 
    
  ptref_cache.insert(ptref_cachet::value_type(ptref, result));
  return result;
}
*/

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

string
smtcheck_opensmt2t::unquote_varname(const string& varname)
{
    int s = varname.length();
    int l = 0;
    if(varname[l] == '|') ++l;
    if(varname[s - 1] == '|')
        return string(varname.begin() + l, varname.begin() + (s - 1));
    return string(varname.begin() + l, varname.end());
}

int
smtcheck_opensmt2t::get_index(const string& _varname)
{
    string varname = unquote_varname(_varname);
    int i = 0;
    int s = varname.length();
    while(i < s && varname[i++] != '#');
    if(i >= s) return -1;
    string num = string(varname.begin() + i, varname.end());
    stringstream ss(num);
    int nnum;
    ss >> nnum;
    return nnum;
}

string
smtcheck_opensmt2t::quote_varname(const string& varname)
{
    if(is_quoted_var(varname)) return varname;

    string ans("");
    assert(varname.length() > 0);
    if(varname[0] != '|')
        ans += '|';
    ans += varname;
    if(varname[varname.length() - 1] != '|')
        ans += '|';
    return ans;
}

void
smtcheck_opensmt2t::adjust_function(smt_itpt& itp, std::vector<symbol_exprt>& common_symbs, string _fun_name)
{
    map<string, PTRef> vars;
    PTRef itp_pt = itp.getInterpolant();

    string fun_name = quote_varname(_fun_name);

    // retrieve variables
    fill_vars(itp_pt, vars);

    // formatted names of common vars
    std::vector<string> quoted_varnames;
    for (std::vector<symbol_exprt>::iterator it = common_symbs.begin(); it != common_symbs.end(); ++it)
    {
        string _var_name = id2string(it->get_identifier());
        string var_name = remove_invalid(_var_name);
        quoted_varnames.push_back(quote_varname(var_name));
    }

    // build substitution map (removing indices)
    // meanwhile, add the vars to Tterm
    Tterm *tterm = new Tterm();
    Map<PTRef,PtAsgn,PTRefHash> subst;

    bool only_common_vars_in_itp = true;
    cout << "; Variables in the interpolant: " << endl;
    for(map<string, PTRef>::iterator it = vars.begin(); it != vars.end(); ++it)
    {
        cout << " * " << it->first << ' ';
        if (quoted_varnames.end() ==
            find (quoted_varnames.begin(), quoted_varnames.end(), it->first)){
            cout << " ---> local var to A; should not be in the interpolant";
            only_common_vars_in_itp = false;
        }

        PTRef var = it->second;
        string new_var_name = remove_index(it->first);
        PTRef new_var = logic->mkVar(logic->getSortRef(var), new_var_name.c_str());
        tterm->addArg(new_var);
        subst.insert(var, PtAsgn(new_var, l_True));
        cout << endl;
    }

    assert(only_common_vars_in_itp);

    // substitute
    PTRef new_root;
    logic->varsubstitute(itp_pt, subst, new_root);
    //cout << "; Formula " << logic->printTerm(itp.getInterpolant()) << " is now " << logic->printTerm(new_root) << endl;
    tterm->setBody(new_root);

    tterm->setName(fun_name);
    //logic->addFunction(tterm);
    //logic->dumpFunction(cout, tterm);
    itp.setTterm(tterm);
    itp.setLogic(logic);
}

void
smtcheck_opensmt2t::fill_vars(PTRef itp, map<string, PTRef>& subst)
{
    set<PTRef> visited;
    queue<PTRef> q;
    q.push(itp);
    while(!q.empty())
    {
        PTRef p = q.front();
        q.pop();
        if(visited.find(p) != visited.end())
            continue;
        if(logic->isVar(p))
            subst[logic->getSymName(p)] = p;
        else
        {
            Pterm& pt = logic->getPterm(p);
            for(int i = 0; i < pt.size(); ++i)
                q.push(pt[i]);
        }
        visited.insert(p);
    }
}

bool
smtcheck_opensmt2t::is_quoted_var(const string& varname)
{
    assert(varname.length() > 0);
    return (varname[0] == '|') && (varname[varname.length() - 1] == '|');
}

string
smtcheck_opensmt2t::remove_invalid(const string& varname)
{
    string ans("");
    for(unsigned int i = 0; i < varname.length(); ++i)
    {
        if(varname[i] != '\\')
            ans += varname[i];
    }
    return ans;
}

string
smtcheck_opensmt2t::remove_index(string var)
{
    int i = var.length() - 1;
    while(i >= 0 && var[i] != '#') --i;
    string no_index;
    if(i > 0)
        no_index = string(var.begin(), var.begin() + i);
    else
        return var;
    if(is_quoted_var(var))
        return quote_varname(no_index);
    return no_index;
}


/*******************************************************************\

Function: smtcheck_opensmt2t::get_interpolant

  Inputs:

 Outputs:

 Purpose: Extracts the symmetric interpolant of the specified set of
 partitions. This method can be called only after solving the
 the formula with an UNSAT result.

\*******************************************************************/
// KE : Shall add the code using new outputs from OpenSMT2 + apply some changes to variable indices
//      if the code is too long split to the method - extract_itp, which is now commented (its body).
void smtcheck_opensmt2t::get_interpolant(const interpolation_taskt& partition_ids, interpolantst& interpolants)
{
  assert(ready_to_interpolate);

  // Set labeling function
  //const char* msg;
  osmt->getConfig().setBooleanInterpolationAlgorithm(itp_algorithm);
  //osmt->getConfig().setOption(SMTConfig::o_itp_bool_alg, SMTOption(itp_algorithm), msg);

  SimpSMTSolver& solver = osmt->getSolver();

  // Create the proof graph
  solver.createProofGraph();

  vector<PTRef> itp_ptrefs;

  // iterative call of getSingleInterpolant:
  produceConfigMatrixInterpolants(partition_ids, itp_ptrefs);

  solver.deleteProofGraph();

  for(unsigned i = 0; i < itp_ptrefs.size(); ++i)
  {
      smt_itpt *new_itp = new smt_itpt();
      extract_itp(itp_ptrefs[i], *new_itp);
      interpolants.push_back(new_itp);
      char *s = logic->printTerm(interpolants.back()->getInterpolant());
      cout << "Interpolant " << i << " = " << s << endl;
      free(s);
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
    //char* msg1;
    //mainSolver->writeSolverState_smtlib2("__SMT_query", &msg1);
  }

  ready_to_interpolate = false;

  if (current_partition != NULL) {
    close_partition();
  }

#ifdef DEBUG_SMT_EUF
  logic->dumpHeaderToFile(cout);
#endif
//  add_variables();
#ifdef DEBUG_SMT_LRA
  /*
  //If have problem with declaration of vars - uncommen this!
  cout << "; XXX SMT-lib --> LRA-Logic Translation XXX" << endl;
  cout << "; Declarations from two source: if there is no diff use only one for testing the output" << endl;
  cout << "; Declarations from Hifrog :" << endl;
  for(it_var_set_str iterator = var_set_str.begin(); iterator != var_set_str.end(); iterator++) {
  	  cout << "(declare-fun " << *iterator << ")" << endl;
  }
  cout << "; Declarations from OpenSMT2 :" << endl;
  */
  logic->dumpHeaderToFile(cout);
  cout << "(assert\n  (and" << endl;
#endif
  char *msg;
  for(int i = pushed_formulas; i < top_level_formulas.size(); ++i) {
#ifdef DEBUG_SMT_EUF
      cout << "\n(assert\n" << logic->printTerm(top_level_formulas[i]) << "\n)" << endl;
#endif
      mainSolver->insertFormula(top_level_formulas[i], &msg);
#ifdef DEBUG_SMT_LRA
      char* s = logic->printTerm(top_level_formulas[i]);
      cout << "; XXX Partition: " << i << endl << "    " << s << endl;
      free(s);
#endif
  }
  pushed_formulas = top_level_formulas.size();
#ifdef DEBUG_SMT_LRA
  for(it_ite_map_str iterator = ite_map_str.begin(); iterator != ite_map_str.end(); iterator++) {
	  cout << "; XXX oite symbol: " << iterator->first << endl << iterator->second << endl;
  }
  cout << "))" << endl << "(check-sat)" << endl;
#endif

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
    if (current_partition->size() >= 1){
      PTRef pand = logic->mkAnd(*current_partition);
#ifdef DEBUG_SMT_LRA
      char* s= logic->printTerm(pand);
      cout << "; Pushing to solver: " << s << endl;
      free(s);
#endif
      top_level_formulas.push(pand);
    } else if (current_partition->size() == 1){
      PTRef pand = (*current_partition)[0];
#ifdef DEBUG_SMT_LRA
      char* s= logic->printTerm(pand);
      cout << "; Pushing to solver: " << s << endl;
      free(s);
#endif
      std::cout << "Trivial partition (terms size = 1): " << partition_count << "\n";
      top_level_formulas.push(pand);
    } /*else {
      // GF: adding (assert true) for debugging only
      top_level_formulas.push(logic->getTerm_true());
    } */
  }

  current_partition = NULL;
}

/*******************************************************************\

Function: smtcheck_opensmt2t::extract_expr_str_number

  Inputs: expression that is a constant (+/-/int/float/rational)

 Outputs: a string of the number

 Purpose: assure we are extracting the number correctly.

 expr.get(ID_C_cformat).c_str() - doesn't work for negative numbers!

\*******************************************************************/
std::string smtcheck_opensmt2t::extract_expr_str_number(const exprt &expr)
{
	std::string const_val = expr.print_number_2smt(); // DO NOT CHANGE TO cprover util code as it works only for positive or unsigned!
	//(unless upgrade, please keep the checks/assert!)
	// If can be that we missed more cases... use the debug prints to check conversions!!
#ifdef DEBUG_SSA_SMT_NUMERIC_CONV
	cout << "; EXTRACTING NUMBER " << const_val << " (ORIG-EXPR " << expr.get(ID_value) << " :: " << expr.type().id() << ")"<< endl;
	cout << "; TEST FOR EXP C FORMAT GIVES " << expr.get(ID_C_cformat).c_str() << " with TYPE " << expr.type().id_string() << endl;
#endif

	return const_val;
}

/*******************************************************************\

Function: smtcheck_opensmt2t::extract_expr_str_number_wt_sign

  Inputs: expression that is a constant (+/-/int/float/rational)

 Outputs: a pair of a number and its sign (true for +, false for -)

 Purpose: to build negative number ptref correctly


\*******************************************************************/
std::pair <std::string, bool> smtcheck_opensmt2t::extract_expr_str_number_wt_sign(const exprt &expr)
{
	std::string const_val = extract_expr_str_number(expr);
	if (const_val.at(0) == '-')
		return std::pair <std::string, bool> (const_val.erase(0,1), false);

	return std::pair <std::string, bool> (const_val, true);
}

/*******************************************************************\

Function: smtcheck_opensmt2t::extract_expr_str_name

  Inputs: expression that is a var

 Outputs: a string of the name

 Purpose: assure we are extracting the name correctly and in one place.

\*******************************************************************/
std::string smtcheck_opensmt2t::extract_expr_str_name(const exprt &expr)
{
	string str = id2string(expr.get(ID_identifier));
	assert (str.size() != 0); // Check the we really got something

	if(expr.id() == ID_nondet_symbol && str.find("nondet") == std::string::npos)
		str = str.replace(0,7, "symex::nondet");

	if (str.find("c::__CPROVER_rounding_mode#") != std::string::npos) {
	#ifdef DEBUG_SSA_SMT // KE - Remove assert if you wish to have debug info
		cout << "; " << str << " :: " << expr.id() << " - Should Not Add Rounding Model\n" << expr.pretty() << endl;
	#else
		cout << "EXIT WITH ERROR: Using Rounding Model in LRA " << str << endl;
		assert(false);
	#endif
	}

	return str;
}

/*******************************************************************\

Function: smtcheck_opensmt2t::dump_on_error

  Inputs: location where the error happened

 Outputs: cout the current smt encoding (what did so far) to the cout

 Purpose: To know what is the problem while encoding the formula

\*******************************************************************/
void smtcheck_opensmt2t::dump_on_error(std::string location) {
	  /*
	  //If have problem with declaration of vars - uncommen this!
	  cout << "; XXX SMT-lib --> LRA-Logic Translation XXX" << endl;
	  cout << "; Declarations from two source: if there is no diff use only one for testing the output" << endl;
	  cout << "; Declarations from Hifrog :" << endl;
	  for(it_var_set_str iterator = var_set_str.begin(); iterator != var_set_str.end(); iterator++) {
	  	  cout << "(declare-fun " << *iterator << ")" << endl;
	  }
	  cout << "; Declarations from OpenSMT2 :" << endl;
	  */
	  logic->dumpHeaderToFile(cout);
	  cout << "(assert\n  (and" << endl;
	  for(int i = 0; i < top_level_formulas.size(); ++i) {
		  char *s = logic->printTerm(top_level_formulas[i]);
	      cout << "; XXX Partition: " << i << endl << "    " << s << endl;
	      free(s);
	  }

	  // If code - once needed uncomment this debug flag in the header
#ifdef DEBUG_SMT_LRA
	  for(it_ite_map_str iterator = ite_map_str.begin(); iterator != ite_map_str.end(); iterator++) {
		  cout << "; XXX oite symbol: " << iterator->first << endl << iterator->second << endl;
	  }
#endif
	  cout << "))" << endl << "(check-sat)" << endl;
}
