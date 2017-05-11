/*******************************************************************\

Module: Wrapper for OpenSMT2. Based on satcheck_minisat.

Author: Grigory Fedyukovich

\*******************************************************************/
#include "smtcheck_opensmt2_lra.h"
#include <util/type.h>

//#define SMT_DEBUG
//#define SMT_DEBUG_VARS_BOUNDS // For debugging the option: type_constraints_level

void smtcheck_opensmt2t_lra::initializeSolver(const char* name)
{
    osmt = new Opensmt(opensmt_logic::qf_lra, name);
    lralogic = &(osmt->getLRALogic());
    logic = &(osmt->getLRALogic());
    mainSolver = &(osmt->getMainSolver());
    
    const char* msg=NULL;
    osmt->getConfig().setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    if (msg==NULL) free((char *)msg);

    // KE: Fix a strange bug can be related to the fact we are pushing
    // a struct into std::vector and use [] before any push_back
    literals.push_back(PTRef());
    literalt l = new_variable(); // Shall be location 0, i.e., [l.var_no()] is [0]
    literals[0] = logic->getTerm_true(); // Which is .x =0
    // KE: End of fix
    
    // To avoid issues with type constraints for LRA
    if (type_constraints_level > 0)
        std::cout << "Adding Type Constraints (" << type_constraints_level << ")" 
                << ((type_constraints_level == 1 ? "for type constraints on non-deterministic input" : ""))
                << ((type_constraints_level == 2 ? "for type constraints on variables" : ""))
                << ((type_constraints_level >= 3  ? "** ERROR ** Unknown Option" : ""))
                << std::endl;
 }

// Free all inner objects
smtcheck_opensmt2t_lra::~smtcheck_opensmt2t_lra()
{
    // Shall/When need to: freeSolver() ?
}

exprt smtcheck_opensmt2t_lra::get_value(const exprt &expr)
{
    if (converted_exprs.find(expr.hash()) != converted_exprs.end()) {
        literalt l = converted_exprs[expr.hash()]; // TODO: might be buggy
        PTRef ptrf = literals[l.var_no()];

        // Get the value of the PTRef
        if (logic->isIteVar(ptrf)) // true/false - evaluation of a branching
        {
            if (smtcheck_opensmt2t::is_value_from_solver_false(ptrf))
                    return false_exprt();
            else
                    return true_exprt();
        }
        else if (logic->isTrue(ptrf)) //true only
        {
            return true_exprt();
        }
        else if (logic->isFalse(ptrf)) //false only
        {
            return false_exprt();
        }
        else if (logic->isVar(ptrf)) // Constant value
        {
            // Create the value
            irep_idt value = 
                    smtcheck_opensmt2t::get_value_from_solver(ptrf);

            // Create the expr with it
            constant_exprt tmp = constant_exprt();
            tmp.set_value(value);
            
            return tmp;
        }
        else if (logic->isConstant(ptrf))
        {
            // Constant?
            irep_idt value = 
                    smtcheck_opensmt2t::get_value_from_solver(ptrf);
            
            // Create the expr with it
            constant_exprt tmp = constant_exprt();
            tmp.set_value(value);

            return tmp;
        }
        else
        {
            assert(0);
        }
    }
    else // Find the value inside the expression - recursive call
    { 
        exprt tmp=expr;

        Forall_operands(it, tmp)
        {
                exprt tmp_op=get_value(*it);
                it->swap(tmp_op);
        }

        return tmp;
    }
}

literalt smtcheck_opensmt2t_lra::const_var_Real(const exprt &expr)
{
    string num = extract_expr_str_number(expr);
    PTRef rconst = PTRef_Undef;
    if(num.size() <= 0)
    {
        if (expr.type().id() == ID_c_enum)
        {
            num = expr.type().find(ID_tag).pretty();
        }
        else if (expr.type().id() == ID_c_enum_tag)
        {
            num = id2string(to_constant_expr(expr).get_value());
        }
        else
        {
            assert(0);
        }
    }
    
    rconst = lralogic->mkConst(num.c_str()); // Can have a wrong conversion sometimes!
    assert(rconst != PTRef_Undef);

    // Check the conversion from string to real was done properly - do not erase!
    assert(!lralogic->isRealOne(rconst) || expr.is_one()); // Check the conversion works: One => one
    if(expr.is_constant() && (expr.is_boolean() || is_number(expr.type()))){
    	exprt temp_check = exprt(expr); temp_check.negate();
        assert(!lralogic->isRealZero(rconst) || (expr.is_zero() || temp_check.is_zero())); // Check the conversion works: Zero => zero
        // If there is a problem usually will fails on Zero => zero since space usually translated into zero :-)
    } else {
    	// Don't check here, it can be a pointer or some address.
    	// Yes, we can have also a bug here
    	//TODO: when support array fully add assert here
    }

    return push_variable(rconst); // Keeps the new PTRef + create for it a new index/literal
}

literalt smtcheck_opensmt2t_lra::const_from_str(const char* num)
{
    PTRef rconst = lralogic->mkConst(num); // Can have a wrong conversion sometimes!
    return push_variable(rconst); // Keeps the new PTRef + create for it a new index/literal
}

literalt smtcheck_opensmt2t_lra::type_cast(const exprt &expr) 
{
    // KE: New Cprover code - patching
    bool is_expr_bool = (expr.is_boolean() || (expr.type().id() == ID_c_bool)); 
    bool is_operands_bool = ((expr.operands())[0].is_boolean() 
                || ((expr.operands())[0].type().id() == ID_c_bool)); 

    // KE: Take care of type cast - recursion of convert take care of it anyhow
    // Unless it is constant bool, that needs different code:
    if (expr.type().id() == (expr.operands())[0].type().id()) {
        return convert((expr.operands())[0]);
    } else if (is_expr_bool && (expr.operands())[0].is_constant()) {
    	std::string val = extract_expr_str_number((expr.operands())[0]);
    	bool val_const_zero = (val.size()==0) || (stod(val)==0.0);
    	return const_var(!val_const_zero);
    } else if (is_number(expr.type()) && is_operands_bool) {
    	// Cast from Boolean to Real - Add
    	literalt lt = convert((expr.operands())[0]); // Creating the Bool expression
    	PTRef ptl = logic->mkIte(literals[lt.var_no()], lralogic->mkConst("1"), lralogic->mkConst("0"));
    	return push_variable(ptl); // Keeps the new literal + index it
    } else if (is_expr_bool && is_number((expr.operands())[0].type())) {
    	// Cast from Real to Boolean - Add
    	literalt lt = convert((expr.operands())[0]); // Creating the Bool expression
    	PTRef ptl = logic->mkNot(logic->mkEq(literals[lt.var_no()], lralogic->mkConst("0")));
    	return push_variable(ptl); // Keeps the new literal + index it
    } else {
    	return convert((expr.operands())[0]);
    }
}

PTRef smtcheck_opensmt2t_lra::mult_real(const exprt &expr, vec<PTRef> &args) 
{
    PTRef ptl;

    bool is_lin_op = isLinearOp(expr,args);
    #ifdef SMT_DEBUG
        assert(is_lin_op);
        ptl = lralogic->mkRealTimes(args);
    #else
        if (!is_lin_op)
            return runsupported2var(expr);

        // If linear op, try to create it
        try
        {
            ptl = lralogic->mkRealTimes(args);
        }
        catch (...)
        { /* We catch and give a nice error message if it is not in debug mode
                 To See the error run with the SMT_DEBUG define on
                 */
            return runsupported2var(expr);
        }
    #endif

    return ptl;
}

PTRef smtcheck_opensmt2t_lra::div_real(const exprt &expr, vec<PTRef> &args) 
{
    PTRef ptl;

    bool is_lin_op = isLinearOp(expr,args);
    bool is_of_legal_form2solver = lralogic->isRealTerm(args[0]) &&  logic->isConstant(args[1]);
    #ifdef SMT_DEBUG
        assert(is_lin_op);
        ptl = lralogic->mkRealDiv(args);
    #else
        if ((!is_lin_op) || (!is_of_legal_form2solver))
            return runsupported2var(expr);

        // If linear op, try to create it
        try
        {
            ptl = lralogic->mkRealDiv(args);
        }
        catch (...)
        { /* We catch and give a nice error message if it is not in debug mode
                 To See the error run with the SMT_DEBUG define on
                 */
            return runsupported2var(expr);
        }
    #endif

    return ptl;
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

    const irep_idt &_id=expr.id(); // KE: gets the id once for performance
    
    /* Check which case it is */
    literalt l;
    if (_id==ID_code) {
        
        l = lunsupported2var(expr);
        
    } else if(_id==ID_symbol || _id==ID_nondet_symbol){
    #ifdef SMT_DEBUG
        cout << "; IT IS A VAR" << endl;
    #endif

        l = lvar(expr);
        
    } else if (_id==ID_constant) {
    #ifdef SMT_DEBUG
        cout << "; IT IS A CONSTANT " << endl;
    #endif

        l = lconst(expr);
        
    } else if (_id == ID_typecast && expr.has_operands()) {
    #ifdef SMT_DEBUG
        bool is_const =(expr.operands())[0].is_constant(); // Will fail for assert(0) if code changed here not carefully!
        cout << "; IT IS A TYPECAST OF " << (is_const? "CONST " : "") << expr.type().id() << endl;
    #endif
        
        l = type_cast(expr);
        
    #ifdef SMT_DEBUG
    char* s = getPTermString(l);
    cout << "; (TYPE_CAST) For " << expr.id() << " Created OpenSMT2 formula " << s << endl;
    free(s);
    #endif
    } else if (_id == ID_typecast) {
    #ifdef SMT_DEBUG
            cout << "EXIT WITH ERROR: operator does not yet supported in the LRA version (token: " << _id << ")" << endl;
            assert(false); // Need to take care of - typecast no operands
    #else
        l = lunsupported2var(expr);
    #endif
    } else if (_id == ID_abs) {
        
        l = labs(expr);
        
    } else { // General case:
    #ifdef SMT_DEBUG
        cout << "; IT IS AN OPERATOR" << endl;

        if (expr.has_operands() && expr.operands().size() > 1) {
        	if ((expr.operands()[0] == expr.operands()[1]) &&
        		(!expr.operands()[1].is_constant())	&&
        		  ((_id == ID_div) ||
        		   (_id == ID_floatbv_div) ||
        	       (_id == ID_mult) ||
        		   (_id == ID_floatbv_mult))
        	){
        		cout << "; IT IS AN OPERATOR BETWEEN SAME EXPR: NOT SUPPORTED FOR NONDET" << endl;
        		assert(false);
			}
		}
#endif
        // Check if for div op there is a rounding variable
        bool is_div_wtrounding = // need to take care differently!
        		((_id == ID_floatbv_minus || _id == ID_minus ||
        		  _id == ID_floatbv_plus || _id == ID_plus ||
                          _id == ID_floatbv_div || _id == ID_div ||
                          _id == ID_floatbv_mult || _id == ID_mult)
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
                                    << _id << ")" << endl;
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
                if((*it).id()==ID_symbol || (*it).id()==ID_nondet_symbol)
                {
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
            ptl = runsupported2var(expr);
        } else if (_id==ID_notequal) {
            ptl = logic->mkNot(logic->mkEq(args));
        } else if(_id == ID_equal) {
            ptl = logic->mkEq(args);
        } else if (_id==ID_if) {
            ptl = logic->mkIte(args);
#ifdef DEBUG_SMT2SOLVER
    ite_map_str.insert(make_pair(string(getPTermString(ptl)),logic->printTerm(logic->getTopLevelIte(ptl))));
#endif
        } else if(_id == ID_ifthenelse) {
            ptl = logic->mkIte(args);
#ifdef DEBUG_SMT2SOLVER
            ite_map_str.insert(make_pair(string(getPTermString(ptl)),logic->printTerm(logic->getTopLevelIte(ptl))));
#endif
        } else if(_id == ID_and) {
            ptl = logic->mkAnd(args);
        } else if(_id == ID_or) {
            ptl = logic->mkOr(args);
        } else if(_id == ID_xor) {
            ptl = logic->mkXor(args);      
        } else if(_id == ID_not) {
            ptl = logic->mkNot(args);
        } else if(_id == ID_implies) {
            ptl = logic->mkImpl(args);
        } else if(_id == ID_ge) {
            ptl = lralogic->mkRealGeq(args);
        } else if(_id == ID_le) {
            ptl = lralogic->mkRealLeq(args);
        } else if(_id == ID_gt) {
            ptl = lralogic->mkRealGt(args);
        } else if(_id == ID_lt) {
            ptl = lralogic->mkRealLt(args);
        } else if(_id == ID_plus) {
            ptl = lralogic->mkRealPlus(args);
        } else if(_id == ID_minus) {
            ptl = lralogic->mkRealMinus(args);
        } else if(_id == ID_unary_minus) {
            ptl = lralogic->mkRealMinus(args);
        } else if(_id == ID_unary_plus) {
            ptl = lralogic->mkRealPlus(args);
        } else if(_id == ID_mult) {
            ptl = mult_real(expr,args);
        } else if(_id == ID_div) {
            ptl = div_real(expr,args);
        } else if(_id == ID_assign) {
            ptl = logic->mkEq(args);
        } else if(_id == ID_ieee_float_equal) {
            ptl = logic->mkEq(args);
        } else if(_id == ID_ieee_float_notequal) {
            ptl = logic->mkNot(logic->mkEq(args));
        } else if(_id == ID_floatbv_plus) {
            ptl = lralogic->mkRealPlus(args);
        } else if(_id == ID_floatbv_minus) {
            ptl = lralogic->mkRealMinus(args);
        } else if(_id == ID_floatbv_div) {
            ptl = div_real(expr,args);
        } else if(_id == ID_floatbv_mult) {
            ptl = mult_real(expr,args);
        } else if(_id == ID_index) {
#ifdef SMT_DEBUG
            cout << "EXIT WITH ERROR: Arrays and index of an array operators have no support yet in the LRA version (token: "
                            << _id << ")" << endl;
            assert(false); // No support yet for arrays
#else
            ptl = runsupported2var(expr);
#endif
        } else if((_id == ID_address_of) || (_id == ID_pointer_object) 
                || (_id == ID_pointer_offset)) {
#ifdef SMT_DEBUG
            cout << "EXIT WITH ERROR: Address and references of, operators have no support yet in the LRA version (token: "
                            << _id << ")" << endl;
            assert(false); // No support yet for arrays
#else
            ptl = runsupported2var(expr);
#endif
        } else {
#ifdef SMT_DEBUG // KE - Remove assert if you wish to have debug info
            cout << _id << ";Don't really know how to deal with this operation:\n" << expr.pretty() << endl;
            cout << "EXIT WITH ERROR: operator does not yet supported in the LRA version (token: "
            		<< _id << ")" << endl;
            assert(false);
#else
            ptl = runsupported2var(expr);
#endif
        }
        
        l = push_variable(ptl); // Keeps the new PTRef + create for it a new index/literal
    }
    converted_exprs[expr.hash()] = l;
#ifdef SMT_DEBUG
    PTRef ptr = literals[l.var_no()];
    char *s = logic->printTerm(ptr);
    cout << "; For " << _id << " Created OpenSMT2 formula " << s << endl;
    free(s);
#endif
    return l;
}

literalt smtcheck_opensmt2t_lra::lnotequal(literalt l1, literalt l2){
    vec<PTRef> args;
    PTRef pl1 = literals[l1.var_no()];
    PTRef pl2 = literals[l2.var_no()];
    args.push(pl1);
    args.push(pl2);
    PTRef ans = logic->mkNot(logic->mkEq(args));
    return push_variable(ans); // Keeps the new PTRef + create for it a new index/literal
}


PTRef smtcheck_opensmt2t_lra::runsupported2var(const exprt expr)
{
    PTRef var;

    const string str = smtcheck_opensmt2t::_unsupported_var_str + std::to_string(unsupported2var++);
    assert(str.size() > 0);
    if ((expr.is_boolean()) || (expr.type().id() == ID_c_bool)) 
        var = logic->mkBoolVar(str.c_str());
    else
        var = lralogic->mkRealVar(str.c_str());

    return var;
}

literalt smtcheck_opensmt2t_lra::lunsupported2var(const exprt expr)
{
    PTRef var = runsupported2var(expr);
    return push_variable(var);
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
    PTRef var;
    assert(str.size() > 0);
    if(is_number(expr.type()))
    	var = lralogic->mkRealVar(str.c_str());
    else if ((expr.is_boolean()) || (expr.type().id() == ID_c_bool)) 
    	var = logic->mkBoolVar(str.c_str());
    else { // Is a function with index, array, pointer
#ifdef SMT_DEBUG
    	cout << "EXIT WITH ERROR: Arrays and index of an array operator have no support yet in the LRA version (token: "
    			<< expr.type().id() << ")" << endl;
    	assert(false); // No support yet for arrays
#else
    	var = runsupported2var(expr);
#endif
    }

    literalt l = push_variable(var); // Keeps the new PTRef + create for it a new index/literal

    if (type_constraints_level > 0)
    	add_constraints2type(expr, var);

#ifdef DEBUG_SMT2SOLVER
	std::string add_var = str + " () " + getVarData(var);
	if (var_set_str.end() == var_set_str.find(add_var)) {
		var_set_str.insert(add_var);
	}
#endif

	return l;
}

literalt smtcheck_opensmt2t_lra::labs(const exprt &expr) 
{
    // ABS - all refers as real
    literalt lt = convert((expr.operands())[0]); // Create the inner part
    PTRef ptl = logic->mkIte(
                        lralogic->mkRealLt(literals[lt.var_no()], lralogic->getTerm_RealZero()),  // IF
                        lralogic->mkRealNeg(literals[lt.var_no()]),                 // Then
                        literals[lt.var_no()]);                                     // Else

    literalt l = push_variable(ptl); // Keeps the new literal + index it

#ifdef SMT_DEBUG
    char* s = getPTermString(l);
    cout << "; (ABS) For " << expr.id() << " Created OpenSMT2 formula " << s << endl;
    free(s);
#endif

    return l;
}

std::string smtcheck_opensmt2t_lra::create_bound_string(std::string base, int exp)
{
    std::string ret = base;
    int size = exp - base.size() + 1; // for format 3.444444
    for (int i=0; i<size;i++)
        ret+= "0";

    return ret;
}

literalt smtcheck_opensmt2t_lra::create_constraints2type(
		PTRef &var,
		std::string lower_b,
		std::string upper_b)
{
    vec<PTRef> args;
    vec<PTRef> args1; args1.push(lralogic->mkConst(lower_b.c_str())); args1.push(var);
    vec<PTRef> args2; args2.push(var); args2.push(lralogic->mkConst(upper_b.c_str()));
    PTRef ptl1 = lralogic->mkRealLeq(args1);
    PTRef ptl2 = lralogic->mkRealLeq(args2);
    literalt l1 = push_variable(ptl1);
    literalt l2 = push_variable(ptl2);

    return land(l1,l2);
}

void smtcheck_opensmt2t_lra::push_assumes2type(
		PTRef &var,
		std::string lower_b,
		std::string upper_b)
{
    if (type_constraints_level < 1 ) return;

    literalt l = create_constraints2type(var, lower_b, upper_b); 
    PTRef ptr = literals[l.var_no()];
    set_to_true(ptr);

#ifdef SMT_DEBUG_VARS_BOUNDS
    char *s = logic->printTerm(ptr);
    cout << "; For Assume Constraints Created OpenSMT2 formula " << s << endl;
    cout << "; For Bounds " << lower_b.c_str() << " and " << upper_b.c_str() << endl;
    free(s);
#endif
}

void smtcheck_opensmt2t_lra::push_asserts2type(
		PTRef &var,
		std::string lower_b,
		std::string upper_b)
{
    if (type_constraints_level < 2) return;

    // Else add the checks
    literalt l = create_constraints2type(var, lower_b, upper_b); 
    PTRef ptr = literals[l.var_no()];

    if (is_var_constraints_empty)
    {
        is_var_constraints_empty = false;
        ptr_assert_var_constraints = ptr;
    }
    else
        ptr_assert_var_constraints = logic->mkAnd(ptr_assert_var_constraints, ptr);

#ifdef SMT_DEBUG_VARS_BOUNDS
    char *s = logic->printTerm(ptr);
    cout << "; For Assert Constraints Created OpenSMT2 formula " << s << endl;
    cout << "; Pushed Formulat For Bounds " << lower_b.c_str() << " and " << upper_b.c_str() << endl;
    free(s);
#endif
}

bool smtcheck_opensmt2t_lra::push_constraints2type(
		PTRef &var,
		bool is_non_det,
		std::string lower_b,
		std::string upper_b)
{
    if (is_non_det) // Add Assume
        push_assumes2type(var, lower_b, upper_b);
    else // Add assert
        push_asserts2type(var, lower_b, upper_b);

    return true;
}

// If the expression is a number adds constraints
void smtcheck_opensmt2t_lra::add_constraints2type(const exprt &expr, PTRef &var)
{
    if(!is_number(expr.type())) return ;

    typet var_type = expr.type(); // Get the current type
    if (var_type.is_nil()) return;

    // Check the id is a var
    assert((expr.id() == ID_nondet_symbol) || (expr.id() == ID_symbol));

    // Start building the constraints
#ifdef SMT_DEBUG_VARS_BOUNDS
    cout << "; For variable " << expr.get(ID_identifier) << " in partition " << partition_count
			<< " try to identify this type "<< var_type.pretty()
			<< ((expr.id() == ID_nondet_symbol) ? " that is non-det symbol" : " that is a regular symbol")
			<< endl;
#endif

    //gets the property
    int size = var_type.get_int("width");
    //const irep_idt type = var_type.get("#c_type");
    const irep_idt &type_id=var_type.id_string();
    bool is_non_det = (expr.id() == ID_nondet_symbol);
#ifdef SMT_DEBUG_VARS_BOUNDS   
    bool is_add_constraints = false;
#endif

    // Start checking what it is
    if(type_id==ID_integer || type_id==ID_natural)
    {
    	assert(0); // need to see an example!
    }
    else if(type_id==ID_rational)
    {
    	assert(0); // need to see an example!
    }
    else if(type_id==ID_unsignedbv) // unsigned int = 32, unsigned long = 64
    {
#ifdef SMT_DEBUG_VARS_BOUNDS
    	cout << "; Adding new constraint for unsigned " << ((size==32) ? "int" : "long") << endl;
#endif
    	std::string lower_bound = "0";
    	std::string upper_bound = ((size==32) ? "4294967295" : "18446744073709551615");
#ifdef SMT_DEBUG_VARS_BOUNDS   
    	is_add_constraints = 
#endif
        push_constraints2type(var, is_non_det, lower_bound, upper_bound);
    }
    else if(type_id==ID_signedbv) // int = 32, long = 64
    {
#ifdef SMT_DEBUG_VARS_BOUNDS
    	cout << "; Adding new constraint for " << ((size==32) ? "int" : "long") << endl;
#endif
    	std::string lower_bound = ((size==32) ? "-2147483648" : "-9223372036854775808");
    	std::string upper_bound = ((size==32) ? "2147483647" : "9223372036854775807");
#ifdef SMT_DEBUG_VARS_BOUNDS   
    	is_add_constraints = 
#endif 
        push_constraints2type(var, is_non_det, lower_bound, upper_bound);
    }
    else if(type_id==ID_fixedbv)
    {
    	assert(0); // need to see an example!
    }
    else if(type_id==ID_floatbv) // float = 32, double = 64
    {
#ifdef SMT_DEBUG_VARS_BOUNDS
    	cout << "; Adding new constraint for unsigned " << ((size==32) ? "float" : "double") << endl;
#endif
    	std::string lower_bound = ((size==32) ?
				("-" + create_bound_string("34028234", 38)) : ("-" + create_bound_string("17976931348623157", 308)));
    	std::string upper_bound = ((size==32) ?
				create_bound_string("34028234", 38) : create_bound_string("17976931348623157", 308));
#ifdef SMT_DEBUG_VARS_BOUNDS   
    	is_add_constraints = 
#endif 
        push_constraints2type(var, is_non_det, lower_bound, upper_bound);
    }
    else
    {
    	assert(0); // need to see an example!
    }

	// For numbers add constraints of upper and lower bounds
#ifdef SMT_DEBUG_VARS_BOUNDS
    if (is_add_constraints)
    	cout << "; Add bounds constraints for type "
			<< var_type.get("#c_type") << " "
			<< var_type.get_int("width") << "bits"
			<< endl;
#endif
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
		count_var += logic->isConstant(args[i]) ? 0 : 1;
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

void smtcheck_opensmt2t_lra::check_ce(std::vector<exprt>& exprs)
{
	// this method is used for testing mostly
	char *msg=NULL;

	for (int i = 0; i < top_level_formulas.size(); i++){
                char *s = logic->printTerm(top_level_formulas[i]);
		cout << "\nCE:  " << s << endl;
                free(s);
		mainSolver->insertFormula(top_level_formulas[i], &msg);
		if (msg !=NULL) { free(msg); msg = NULL; }
	}
	mainSolver->push();

	bool res = true;
	unsigned int i = 0;
	while (i < exprs.size() && res){
	    literalt l = convert(exprs[i]);
	    PTRef lp = literals[l.var_no()];
	    mainSolver->insertFormula(lp, &msg);
	    if (msg !=NULL) { free(msg); msg = NULL; }
	    res = (s_True == mainSolver->check());
	    if (!res){
	    	cout << "\n  Problem could be here: " << logic->printTerm(lp) << endl;
	    }
//	    mainSolver->pop();  // TODO: uncomment this line and comment "&& res" in the guard
	    					// to get a segmfalut in the incremental solver
	    i++;
    }
}
