/*******************************************************************\

Module: Wrapper for OpenSMT2. Based on satcheck_minisat.

Author: Grigory Fedyukovich

\*******************************************************************/
#include "smtcheck_opensmt2_lra.h"
#include <util/type.h>
#include <funfrog/utils/naming_helpers.h>

// Debug flags of this class:
//#define SMT_DEBUG
//#define SMT_DEBUG_VARS_BOdUNDS // For debugging the option: type_constraints_level

/*******************************************************************\

Function: smtcheck_opensmt2t_lra::initializeSolver

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void smtcheck_opensmt2t_lra::initializeSolver(const char* name)
{
    osmt = new Opensmt(opensmt_logic::qf_lra, name);
    lralogic = &(osmt->getLRALogic());
    logic = &(osmt->getLRALogic());
    mainSolver = &(osmt->getMainSolver());
    
    const char* msg = nullptr;
    osmt->getConfig().setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    // msg is not allocated, do not free it!
    assert(strcmp(msg, "ok") == 0);

    // To avoid issues with type constraints for LRA
    if (type_constraints_level > 0)
        std::cout << "Adding Type Constraints (" << type_constraints_level << ")" 
                << ((type_constraints_level == 1 ? " for type constraints on non-deterministic input" : ""))
                << ((type_constraints_level == 2 ? " for type constraints on variables" : ""))
                << ((type_constraints_level >= 3  ? " ** ERROR ** Unknown Option" : ""))
                << std::endl;
}

/*******************************************************************\

Function: smtcheck_opensmt2t_lra::~smtcheck_opensmt2t_lra

  Inputs:

 Outputs:

 Purpose: Free all inner objects

\*******************************************************************/
smtcheck_opensmt2t_lra::~smtcheck_opensmt2t_lra()
{
    // Shall/When need to: freeSolver() ?
}

/*******************************************************************\

Function: smtcheck_opensmt2t_lra::const_var_Real

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef smtcheck_opensmt2t_lra::numeric_constant(const exprt & expr)
{
    std::string num = extract_expr_str_number(expr);
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
    assert(!lralogic->isRealOne(rconst) || expr.is_one() || // Check the conversion works: One => one
            (expr.type().id()==ID_c_enum || expr.type().id()==ID_c_enum_tag)); // Cannot check enums
    if(expr.is_constant() && (expr.is_boolean() || is_number(expr.type()))){
    	exprt temp_check = exprt(expr); temp_check.negate();
        assert(!lralogic->isRealZero(rconst) || (expr.is_zero() || temp_check.is_zero())); // Check the conversion works: Zero => zero
        // If there is a problem usually will fails on Zero => zero since space usually translated into zero :-)
    } else if (expr.type().id() == ID_pointer) {
        // when support pointers - change here too
        // KE: not sure which code shall be here
    } else {
    	// Don't check here, it can be a pointer or some address.
    	// Yes, we can have also a bug here
    	//TODO: when support array fully add assert here
        //std::cout << expr.pretty() << std::endl;
        assert(0); // KE: check when get it. Please show me
    }

    return rconst;
}

/*******************************************************************\

Function: smtcheck_opensmt2t_lra::const_from_str

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
literalt smtcheck_opensmt2t_lra::const_from_str(const char* num)
{
    PTRef rconst = lralogic->mkConst(num); // Can have a wrong conversion sometimes!
    return push_variable(rconst); // Keeps the new PTRef + create for it a new index/literal
}

/*******************************************************************\

Function: smtcheck_opensmt2t_lra::type_cast

  Inputs:

 Outputs:

 Purpose:
 * 
 All is Real in LRA so suppose to work id number to number
\*******************************************************************/
PTRef smtcheck_opensmt2t_lra::type_cast(const exprt & expr)
{
    // KE: New Cprover code - patching
    bool is_expr_bool = is_boolean(expr);
    bool is_operands_bool = is_boolean(expr.operands()[0]);

    // KE: Take care of type cast - recursion of convert take care of it anyhow
    // Unless it is constant bool, that needs different code:
    if (expr.type().id() == (expr.operands())[0].type().id()) {
        return expression_to_ptref((expr.operands())[0]);
    } else if (is_expr_bool && (expr.operands())[0].is_constant()) {
    	std::string val = extract_expr_str_number((expr.operands())[0]);
    	bool val_const_zero = (val.size()==0) || (stod(val)==0.0);
    	return constant_bool(!val_const_zero);
    } else if (is_number(expr.type()) && is_operands_bool) {
    	// Cast from Boolean to Real - Add
        PTRef operand_ptref = expression_to_ptref((expr.operands())[0]); // Creating the Bool expression
    	PTRef ptl = logic->mkIte(operand_ptref, lralogic->mkConst("1"), lralogic->mkConst("0"));
      
#ifdef DISABLE_OPTIMIZATIONS
        if (dump_pre_queries)
        {
            // if the condition evaluated to constant, no ite was created
            if(logic->isIte(ptl))
            {
              char *s = logic->printTerm(logic->getTopLevelIte(ptl));
              ite_map_str.insert(make_pair(string(getPTermString(ptl)),std::string(s)));
              //cout << "; XXX oite symbol (type-cast): (" << ite_map_str.size() << ")"
              //    << string(getPTermString(ptl)) << endl << s << endl;
              free(s);
            }
        }
#endif        
        
    	return ptl;
    } else if (is_expr_bool && is_number((expr.operands())[0].type())) {
    	// Cast from Real to Boolean - Add
    	PTRef operand_ptref = expression_to_ptref((expr.operands())[0]); // Creating the Bool expression
    	PTRef ptl = logic->mkNot(logic->mkEq(operand_ptref, lralogic->mkConst("0")));
    	return ptl;
    } else { // All types of number to number, will take the inner value as the converted one
    	return expression_to_ptref((expr.operands())[0]);
    }
}

/*******************************************************************\

Function: smtcheck_opensmt2t_lra::mult_real

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef smtcheck_opensmt2t_lra::mult_real(const exprt &expr, vec<PTRef> &args) 
{
    bool is_lin_op = isLinearOp(expr,args);
    #ifdef SMT_DEBUG
        assert(is_lin_op);
        ptl = lralogic->mkRealTimes(args);
    #else
        if (!is_lin_op)
        {
            PTRef ptl_uns = unsupported_to_var(expr);
            
            // Add new equation of an unknown function (acording to name)
            //PTRef var_eq = create_equation_for_unsupported(expr);
            //set_to_true(logic->mkEq(ptl_uns,var_eq)); // (= |hifrog::c::unsupported_op2var#0| (op operand0 operand1)) 
            // Remove - consider again only when we have UF with LRA works

            return ptl_uns;
        }

        // If linear op, try to create it
        PTRef ptl;
        try
        {
            ptl = lralogic->mkRealTimes(args);
        }
        catch (...)
        { /* We catch and give a nice error message if it is not in debug mode
                 To See the error run with the SMT_DEBUG define on
                 */
            PTRef ptl_uns = unsupported_to_var(expr);
            
            // Add new equation of an unknown function (acording to name)
            //PTRef var_eq = create_equation_for_unsupported(expr);
            //set_to_true(logic->mkEq(ptl_uns,var_eq)); // (= |hifrog::c::unsupported_op2var#0| (op operand0 operand1)) 
            // Remove - consider again only when we have UF with LRA works            

            return ptl_uns;
        }
    #endif

    return ptl;
}

/*******************************************************************\

Function: smtcheck_opensmt2t_lra::div_real

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef smtcheck_opensmt2t_lra::div_real(const exprt &expr, vec<PTRef> &args) 
{
    bool is_lin_op = isLinearOp(expr,args);
    bool is_of_legal_form2solver = lralogic->isRealTerm(args[0]) &&  logic->isConstant(args[1]);
    #ifdef SMT_DEBUG
        assert(is_lin_op);
        ptl = lralogic->mkRealDiv(args);
    #else
        if ((!is_lin_op) || (!is_of_legal_form2solver))
        {
            PTRef ptl_uns = unsupported_to_var(expr);

            // Add new equation of an unknown function (acording to name)
            //PTRef var_eq = create_equation_for_unsupported(expr);
            //set_to_true(logic->mkEq(ptl_uns,var_eq)); // (= |hifrog::c::unsupported_op2var#0| (op operand0 operand1)) 
            // Remove - consider again only when we have UF with LRA works            

            return ptl_uns;
        }

        // If linear op, try to create it
        PTRef ptl;
        try
        {
            ptl = lralogic->mkRealDiv(args);
        }
        catch (...)
        { /* We catch and give a nice error message if it is not in debug mode
                 To See the error run with the SMT_DEBUG define on
                 */
            PTRef ptl_uns = unsupported_to_var(expr);
                        
            // Add new equation of an unknown function (acording to name)
            //PTRef var_eq = create_equation_for_unsupported(expr);
            //set_to_true(logic->mkEq(ptl_uns,var_eq)); // (= |hifrog::c::unsupported_op2var#0| (op operand0 operand1)) 
            // Remove - consider again only when we have UF with LRA works            

            return ptl_uns;
        }
    #endif

    return ptl;
}

/*******************************************************************\

Function: smtcheck_opensmt2t_lra::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef smtcheck_opensmt2t_lra::expression_to_ptref(const exprt & expr)
{
// GF: disabling hash for a while, since it leads to bugs at some particular cases,
//     e.g., for (= |goto_symex::guard#3| (< |c::f::a!0#7| 10))
//           and (= |goto_symex::guard#4| (< |c::f::a!0#11| 10))
//
//    if(converted_exprs.find(expr.hash()) != converted_exprs.end())
//        return converted_exprs[expr.hash()];

    PTRef ptref = get_from_cache(expr);
    if(ptref != PTRef_Undef) { return ptref; }

    const irep_idt & _id = expr.id();
    
    /* Check which case it is */
    if (_id==ID_code || expr.type().id()==ID_code) { //Init structs, arrays etc.
        
        ptref = unsupported_to_var(expr);
        // NO support to this type

    } else if (_id==ID_address_of) {

        ptref = unsupported_to_var(expr);
        // NO support to this type
     
    } else if(_id==ID_symbol || _id==ID_nondet_symbol){

        ptref = symbol_to_ptref(expr);
        
    } else if (_id==ID_constant) {
        ptref = constant_to_ptref(expr);
        
    } else if ((_id == ID_typecast || _id == ID_floatbv_typecast) && expr.has_operands()) {
        ptref = type_cast(expr);
    } else if (_id == ID_typecast || _id == ID_floatbv_typecast) {
    #ifdef SMT_DEBUG
        std::cout << "EXIT WITH ERROR: operator does not yet supported in the LRA version (token: " << _id << ")\n";
        assert(false); // Need to take care of - typecast no operands
    #else
        ptref =unsupported_to_var(expr);
        // TODO: write a better supoort here
    #endif
    } else if (_id == ID_abs) {
        
        ptref = abs_to_ptref(expr);
        
    } else { // General case:
        // Check if for div op there is a rounding variable
        bool is_div_wtrounding = // need to take care differently!
        		((_id == ID_floatbv_div || _id == ID_div ||
                          _id == ID_floatbv_mult || _id == ID_mult)
                        &&
                        ((expr.operands()).size() > 2));

        vec<PTRef> args;
        int i = 0;
        bool is_no_support = false;
        for(auto const & operand : expr.operands())
        {
            assert(!is_cprover_rounding_mode_var(operand)); // KE: we remove this before!
            if (is_div_wtrounding && i >= 2)
            {
            #ifdef SMT_DEBUG
                cout << "EXIT WITH ERROR: * and / operators with more than 2 arguments have no support yet in the LRA version (token: "
                                << _id << ")" << endl;
                assert(false); // No support yet for rounding operator
            #else
                is_no_support = true; // Will cause to over approx all
            #endif
            }
            else
            { 
                // All the rest of the operators
                PTRef cp = expression_to_ptref(operand);
                assert(cp != PTRef_Undef);
                args.push(cp);
                i++; // Only if really add an item to mult/div inc the counter
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
                    if((*it).id() == ID_nondet_symbol && (str_expr2.find(NONDET) != std::string::npos))
                            str_expr2 = str_expr2.insert(7, SYMEX_NONDET);
                    assert(str_expr1.compare(str_expr2) == 0);
                }
                free(s);
#endif
            }
        }

        if (is_no_support) { // If we don't supposrt the operator due to more than 2 args
            ptref = unsupported_to_var(expr);
            
            // Add new equation of an unknown function (acording to name)
            //PTRef var_eq = create_equation_for_unsupported(expr);
            //set_to_true(logic->mkEq(ptref,var_eq)); // (= |hifrog::c::unsupported_op2var#0| (op operand0 operand1))
            // Remove - consider again only when we have UF with LRA works
        } else if (_id==ID_notequal) {
            ptref = logic->mkNot(logic->mkEq(args));
        } else if(_id == ID_equal) {
            ptref = logic->mkEq(args);
        } else if (_id==ID_if) {
            assert(args.size() >= 2); // KE: check the case if so and add the needed code!
            
            // If a then b, (without else) is a => b
            if (args.size() == 2)
            { 
                ptref = logic->mkImpl(args);
            } else {
                ptref = logic->mkIte(args);
                
#ifdef DISABLE_OPTIMIZATIONS
                if (dump_pre_queries)
                {
                    char *s = logic->printTerm(logic->getTopLevelIte(ptref));
                    ite_map_str.insert(make_pair(string(getPTermString(ptref)),std::string(s)));
                    //cout << "; XXX oite symbol: (" << ite_map_str.size() << ")" 
                    //    << string(getPTermString(ptref)) << endl << s << endl;
                    free(s); s=NULL;    
                }
#endif
            }
        } else if(_id == ID_ifthenelse) {
            assert(args.size() >= 3); // KE: check the case if so and add the needed code!
            ptref = logic->mkIte(args);
            
#ifdef DISABLE_OPTIMIZATIONS
            if (dump_pre_queries)
            {
                char *s = logic->printTerm(logic->getTopLevelIte(ptref));
                ite_map_str.insert(make_pair(string(getPTermString(ptref)),std::string(s)));
                //cout << "; XXX oite symbol: (" << ite_map_str.size() << ")" 
                //        << string(getPTermString(ptref)) << endl << s << endl;
                free(s); s=NULL;    
            }
#endif
        } else if(_id == ID_and) {
            ptref = logic->mkAnd(args);
        } else if(_id == ID_or) {
            ptref = logic->mkOr(args);
        } else if(_id == ID_xor) {
            ptref = logic->mkXor(args);
        } else if(_id == ID_not) {
            ptref = logic->mkNot(args);
        } else if(_id == ID_implies) {
            ptref = logic->mkImpl(args);
        } else if(_id == ID_ge) {
            assert(args.size() == 2); // KE: get errors before opensmt
            ptref = lralogic->mkRealGeq(args);
        } else if(_id == ID_le) {
            assert(args.size() == 2); // KE: get errors before opensmt
            ptref = lralogic->mkRealLeq(args);
        } else if(_id == ID_gt) {
            assert(args.size() == 2); // KE: get errors before opensmt 
            ptref = lralogic->mkRealGt(args);
        } else if(_id == ID_lt) {
            assert(args.size() == 2); // KE: get errors before opensmt
            ptref = lralogic->mkRealLt(args);
        } else if(_id == ID_plus) {
            ptref = lralogic->mkRealPlus(args);
        } else if(_id == ID_minus) {
            assert(args.size() == 2); // KE: check before opensmt, to locate better errors
            ptref = lralogic->mkRealMinus(args);
        } else if(_id == ID_unary_minus) {
            assert(args.size() == 1); // KE: check before opensmt, to locate better errors
            ptref = lralogic->mkRealMinus(args);
        } else if(_id == ID_unary_plus) {
            ptref = lralogic->mkRealPlus(args);
        } else if(_id == ID_mult) {
            ptref = mult_real(expr,args);
        } else if(_id == ID_div) {
            ptref = div_real(expr,args);
        } else if(_id == ID_assign) {
            ptref = logic->mkEq(args);
        } else if(_id == ID_ieee_float_equal) {
            ptref = logic->mkEq(args);
        } else if(_id == ID_ieee_float_notequal) {
            ptref = logic->mkNot(logic->mkEq(args));
        } else if(_id == ID_floatbv_plus) {
            ptref = lralogic->mkRealPlus(args);
        } else if(_id == ID_floatbv_minus) {
            assert(args.size() <= 2); // KE: check before opensmt, to locate better errors
            ptref = lralogic->mkRealMinus(args);
        } else if(_id == ID_floatbv_div) {
            ptref = div_real(expr,args);
        } else if(_id == ID_floatbv_mult) {
            ptref = mult_real(expr,args);
        } else if(_id == ID_index) {
#ifdef SMT_DEBUG
            cout << "EXIT WITH ERROR: Arrays and index of an array operators have no support yet in the LRA version (token: "
                            << _id << ")" << endl;
            assert(false); // No support yet for arrays
#else
            ptref = unsupported_to_var(expr);
                        
            // Add new equation of an unknown function (acording to name)
            //PTRef var_eq = create_equation_for_unsupported(expr);
            //set_to_true(logic->mkEq(ptref,var_eq)); // (= |hifrog::c::unsupported_op2var#0| (op operand0 operand1))
            // Remove - consider again only when we have UF with LRA works 
#endif
        } else if((_id == ID_address_of) || (_id == ID_pointer_offset)) {
#ifdef SMT_DEBUG
            cout << "EXIT WITH ERROR: Address and references of, operators have no support yet in the LRA version (token: "
                            << _id << ")" << endl;
            assert(false); // No support yet for address and pointers
#else
            ptref = unsupported_to_var(expr);
                                             
            // Add new equation of an unknown function (acording to name)
            //PTRef var_eq = create_equation_for_unsupported(expr);
            //set_to_true(logic->mkEq(ptref,var_eq)); // (= |hifrog::c::unsupported_op2var#0| (op operand0 operand1))
            // Remove - consider again only when we have UF with LRA works 
#endif
        } else if (_id == ID_pointer_object) {
#ifdef SMT_DEBUG
            cout << "EXIT WITH ERROR: Address and references of, operators have no support yet in the LRA version (token: "
                            << _id << ")" << endl;
            assert(false); // No support yet for pointers
#else
            ptref = unsupported_to_var(expr);
            // TODO: add UF equation to describe the inner part
#endif
        } else if (_id==ID_array) {
#ifdef SMT_DEBUG
            cout << "EXIT WITH ERROR: Arrays and index of an array operators have no support yet in the LRA version (token: "
                            << _id << ")" << endl;
            assert(false); // No support yet for arrays
#else
            ptref = unsupported_to_var(expr);
            // TODO: add UF equation to describe the inner part
            // todo: ADD HERE SUPPORT FOR ARRAYS.
#endif
        } else if((_id == ID_member) || 
                (_id == ID_C_member_name) ||
                (_id == ID_with) ||
                (_id == ID_member_name)) {
#ifdef SMT_DEBUG
            cout << "EXIT WITH ERROR:member operator has no support yet in the UF version (token: "
                << _id << ")" << endl;
            assert(false); // No support yet for arrays
#else
            ptref = unsupported_to_var(expr);
            // TODO
#endif            
        } else {
#ifdef SMT_DEBUG // KE - Remove assert if you wish to have debug info
            cout << _id << ";Don't really know how to deal with this operation:\n" << expr.pretty() << endl;
            cout << "EXIT WITH ERROR: operator does not yet supported in the LRA version (token: "
            		<< _id << ")" << endl;
            assert(false);
#else
            ptref = unsupported_to_var(expr);
            
            // Add new equation of an unknown function (acording to name)
            //PTRef var_eq = create_equation_for_unsupported(expr);
            //set_to_true(logic->mkEq(ptref,var_eq)); // (= |hifrog::c::unsupported_op2var#0| (op operand0 operand1))
            // Remove - consider again only when we have UF with LRA works
#endif
        }
    }
    assert(ptref != PTRef_Undef);
    store_to_cache(expr, ptref);
    return ptref;
}

/*******************************************************************\

Function: smtcheck_opensmt2t_lra::unsupported_to_var

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef smtcheck_opensmt2t_lra::unsupported_to_var(const exprt &expr)
{
    auto it = unsupported_expr2ptrefMap.find(expr);
    if( it != unsupported_expr2ptrefMap.end()) { return it->second;}
    // Create a new unsupported var
    const std::string str = create_new_unsupported_var(expr.type().id().c_str());

    const PTRef var = is_boolean(expr) ? logic->mkBoolVar(str.c_str()) : new_num_var(str);
    store_new_unsupported_var(expr, var);
    return var;
}

PTRef smtcheck_opensmt2t_lra::new_num_var(const std::string & var_name) {
    return lralogic->mkRealVar(var_name.c_str());
}

/*******************************************************************\

Function: smtcheck_opensmt2t_lra::labs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef smtcheck_opensmt2t_lra::abs_to_ptref(const exprt & expr)
{
    // ABS - all refers as real
    PTRef inner = expression_to_ptref((expr.operands())[0]); // Create the inner part
    PTRef ptl = logic->mkIte(
                        lralogic->mkRealLt(inner, lralogic->getTerm_RealZero()),  // IF
                        lralogic->mkRealNeg(inner),                 // Then
                        inner);                                     // Else

#ifdef DISABLE_OPTIMIZATIONS
    if (dump_pre_queries)
    {
        char *s = logic->printTerm(logic->getTopLevelIte(ptl));
        ite_map_str.insert(make_pair(string(getPTermString(ptl)),std::string(s)));
        //cout << "; XXX oite symbol (labs):  (" << ite_map_str.size() << ")" 
        //            << string(getPTermString(ptl)) << endl << s << endl;
        free(s); s=NULL;        
    }
#endif
    return ptl;
}

/*******************************************************************\

Function: smtcheck_opensmt2t_lra::create_constraints2type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
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

/*******************************************************************\

Function: smtcheck_opensmt2t_lra::push_assumes2type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void smtcheck_opensmt2t_lra::push_assumes2type(
		PTRef &var,
		std::string lower_b,
		std::string upper_b)
{
    if (type_constraints_level < 1 ) return;

    literalt l = create_constraints2type(var, lower_b, upper_b); 
    PTRef ptr = ptrefs[l.var_no()];
    set_to_true(ptr);

#ifdef SMT_DEBUG_VARS_BOUNDS
    char *s = logic->printTerm(ptr);
    cout << "; For Assume Constraints Created OpenSMT2 formula " << s << endl;
    cout << "; For Bounds " << lower_b.c_str() << " and " << upper_b.c_str() << endl;
    free(s); s=NULL;
#endif
}

/*******************************************************************\

Function: smtcheck_opensmt2t_lra::push_asserts2type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void smtcheck_opensmt2t_lra::push_asserts2type(
		PTRef &var,
		std::string lower_b,
		std::string upper_b)
{
    if (type_constraints_level < 2) return;

    // Else add the checks
    literalt l = create_constraints2type(var, lower_b, upper_b); 
    PTRef ptr = ptrefs[l.var_no()];
    ptr_assert_var_constraints = logic->mkAnd(ptr_assert_var_constraints, ptr);

#ifdef SMT_DEBUG_VARS_BOUNDS
    char *s = logic->printTerm(ptr);
    cout << "; For Assert Constraints Created OpenSMT2 formula " << s << endl;
    cout << "; Pushed Formulat For Bounds " << lower_b.c_str() << " and " << upper_b.c_str() << endl;
    free(s); s=NULL;
#endif
}

/*******************************************************************\

Function: smtcheck_opensmt2t_lra::push_constraints2type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
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

/*******************************************************************\

Function: smtcheck_opensmt2t_lra::add_constraints2type

  Inputs:

 Outputs:

 Purpose: If the expression is a number adds constraints

\*******************************************************************/
void smtcheck_opensmt2t_lra::add_constraints2type(const exprt &expr, PTRef& var)
{
    typet var_type = expr.type(); // Get the current type
    const irep_idt type_id_c = var_type.get("#c_type");
    const irep_idt &type_id=var_type.id_string();
    
#ifdef SMT_DEBUG_VARS_BOUNDS
    std::cout << "; Try to add type constraints to " << type_id << std::endl;
#endif
    
    /* Test if needs to add */
    if(!is_number(expr.type())) return; // KE: shall also catch the case of char
    if (var_type.is_nil()) return;
    if (expr.is_constant()) return;

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
    int size = var_type.get_unsigned_int("width");
    bool is_non_det = (expr.id() == ID_nondet_symbol);
#ifdef SMT_DEBUG_VARS_BOUNDS   
    bool is_add_constraints = false;
#endif

    // Start checking what it is
    if (type_id_c == ID_signed_char)
    {
#ifdef SMT_DEBUG_VARS_BOUNDS
    	cout << "; Adding new constraint for char signed" << endl;
#endif
        // Is from -128 to 127
    	std::string lower_bound = "-128";
    	std::string upper_bound = "127";
#ifdef SMT_DEBUG_VARS_BOUNDS   
    	is_add_constraints = 
#endif 
        push_constraints2type(var, is_non_det, lower_bound, upper_bound);
    }
    else if (type_id_c == ID_unsigned_char)
    {
#ifdef SMT_DEBUG_VARS_BOUNDS
    	cout << "; Adding new constraint for char unsigned" << endl;
#endif
        // Is from 0 to 255
    	std::string lower_bound = "0";
    	std::string upper_bound = "255";
#ifdef SMT_DEBUG_VARS_BOUNDS   
    	is_add_constraints = 
#endif 
        push_constraints2type(var, is_non_det, lower_bound, upper_bound);
    }    
    else if (type_id_c == ID_char)
    {
#ifdef SMT_DEBUG_VARS_BOUNDS
    	cout << "; Adding new constraint for char " << ((type_id==ID_signedbv) ? "signed" : "unsigned") << endl;
#endif
    	std::string lower_bound = ((type_id==ID_signedbv) ? "-128" : "0");
        std::string upper_bound = ((type_id==ID_signedbv) ? "127" : "255");
        
#ifdef SMT_DEBUG_VARS_BOUNDS   
    	is_add_constraints = 
#endif 
        push_constraints2type(var, is_non_det, lower_bound, upper_bound);
    }
    else if(type_id==ID_integer || type_id==ID_natural)
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
        // The implementation contains support to: 16,32 and 64 bits only
        assert("Data numerical type constraints for bytes are valid for 32,64,128,256 bit-width or up" 
                && (size == 16 || size == 32 || size == 64));
            
    	std::string lower_bound = "0";
    	std::string upper_bound = ((size==64) ? "18446744073709551615" : 
                                        ((size==32) ? "4294967295" : "65535"));
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
        // The implementation contains support to: 16,32 and 64 bits only
        assert("Data numerical type constraints for bytes are valid for 32,64,128,256 bit-width or up" 
            && (size == 16 || size == 32 || size == 64));

        std::string lower_bound = ((size==64) ? "-9223372036854775808" : 
                            ((size==32) ? "-2147483648" : "-32768"));
        std::string upper_bound = ((size==64) ? "9223372036854775807" : 
                            ((size==32) ? "2147483647" : "32767"));
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
        // The implementation contains support to: 32 and 64 bits only
        assert("Data numerical type constraints for bytes are valid for 32,64,128,256 bit-width or up" 
                    && (size == 32 || size == 64));
        
    	std::string lower_bound = ((size==32) ?
				("-" + create_bound_string("34028234", 38)) : ("-" + create_bound_string("17976931348623158", 308)));
    	std::string upper_bound = ((size==32) ?
				create_bound_string("34028233", 38) : create_bound_string("17976931348623157", 308));
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
            << var_type.get_unsigned_int("width") << "bits"
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
            bool is_linear = (logic->isConstant(args[i]) || 
                                lralogic->isRealTerm(args[i]) || 
                                lralogic->isRealPlus(args[i]) || 
                                lralogic->isUF(args[i]));
            count_var += is_linear ? 0 : 1;
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

// Check if a literal is non-linear in the solver side
bool smtcheck_opensmt2t_lra::is_non_linear_operator(PTRef tr)
{
    if (!lralogic->isRealDiv(tr) && !lralogic->isRealTimes(tr))
        return false;
    
    // Get the original vars
    const Pterm& t = logic->getPterm(tr);
    if (t.size() < 2)
        return false;
    
    // If we have 2 or more, than we can check if all constant but one
    int count_var = 0;
    for (int i = 0; i < t.size(); i++) {
        if (!logic->isConstant(t[i]) && !lralogic->isRealConst(t[i]))
            count_var++;
    }
    
    return (count_var > 1);
}

/*******************************************************************\

Function: smtcheck_opensmt2t_lra::check_ce

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void smtcheck_opensmt2t_lra::check_ce(std::vector<exprt>& exprs)
{
	// this method is used for testing mostly
	char *msg = nullptr;

	for (int i = 0; i < top_level_formulas.size(); i++){
	    char *s = logic->printTerm(top_level_formulas[i]);
		std::cout << "\nCE:  " << s << '\n';
        free(s);
		mainSolver->insertFormula(top_level_formulas[i], &msg);
		if (msg !=nullptr) { free(msg); msg = nullptr; }
	}
	mainSolver->push();

	bool res = true;
	unsigned int i = 0;
	while (i < exprs.size() && res){
	    PTRef lp = expression_to_ptref(exprs[i]);
	    mainSolver->insertFormula(lp, &msg);
	    if (msg != nullptr) { free(msg); msg = nullptr; }
	    res = (s_True == mainSolver->check());
	    if (!res){
                char *s = logic->printTerm(lp);
	    	std::cout << "\n  Problem could be here: " << s << '\n';
                free(s);
	    }
//	    mainSolver->pop();  // TODO: uncomment this line and comment "&& res" in the guard
	    					// to get a segmfalut in the incremental solver
	    i++;
    }
}

/*******************************************************************\

Function: smtcheck_opensmt2t_lra::getStringSMTlibDatatype

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
std::string smtcheck_opensmt2t_lra::getStringSMTlibDatatype(const typet& type)
{ 
    if ((type.id()==ID_bool) || (type.id() == ID_c_bool))
        return SMTConstants::SMT_BOOL;
    if (is_number(type))
        return SMTConstants::SMT_REAL;
    
    return SMTConstants::SMT_UNKNOWN; // Shall not get here
}

/*******************************************************************\

Function: smtcheck_opensmt2t_lra::getSMTlibDatatype

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
SRef smtcheck_opensmt2t_lra::getSMTlibDatatype(const typet& type)
{ 
    if ((type.id()==ID_bool) || (type.id() == ID_c_bool))
        return lralogic->getSort_bool(); //SMT_BOOL
    if (is_number(type))
        return lralogic->getSort_real(); // SMT_REAL

    throw std::logic_error("Unknown datatype encountered!");
}
