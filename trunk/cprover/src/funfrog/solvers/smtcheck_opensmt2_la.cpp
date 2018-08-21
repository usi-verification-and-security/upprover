/*******************************************************************\

Module: Wrapper for OpenSMT2. Based on satcheck_minisat.

Author: Grigory Fedyukovich

\*******************************************************************/
#include "smtcheck_opensmt2_la.h"
#include <util/type.h>
#include "../hifrog.h"
#include <funfrog/utils/naming_helpers.h>


// Debug flags of this class:
//#define SMT_DEBUG
//#define SMT_DEBUG_VARS_BOUNDS // For debugging the option: type_constraints_level

/*******************************************************************\

Function: smtcheck_opensmt2t_la::~smtcheck_opensmt2t_la

  Inputs:

 Outputs:

 Purpose: Free all inner objects

\*******************************************************************/
smtcheck_opensmt2t_la::~smtcheck_opensmt2t_la()
{
    // Shall/When need to: freeSolver() ?
}

/*******************************************************************\

Function: smtcheck_opensmt2t_la::get_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
exprt smtcheck_opensmt2t_la::get_value(const exprt &expr)
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
            throw std::logic_error("Unknown case encountered in get_value");
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

/*******************************************************************\

Function: smtcheck_opensmt2t_la::lconst_number

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
literalt smtcheck_opensmt2t_la::lconst_number(const exprt &expr)
{
    std::string num = extract_expr_str_number(expr);
    PTRef rconst = lalogic->mkConst(num.c_str()); // Can have a wrong conversion sometimes!
    assert(rconst != PTRef_Undef);

    // Check the conversion from string to real was done properly - do not erase!
    assert(!lalogic->isNumOne(rconst) || expr.is_one() || // Check the conversion works: One => one
            (expr.type().id()==ID_c_enum || expr.type().id()==ID_c_enum_tag || expr.type().id()==ID_c_bit_field)); // Cannot check enums
    if(expr.is_constant() && (expr.is_boolean() || is_number(expr.type()))){
    	exprt temp_check = exprt(expr); temp_check.negate();
        assert(!lalogic->isNumZero(rconst) || (expr.is_zero() || temp_check.is_zero())); // Check the conversion works: Zero => zero
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

    return push_variable(rconst); // Keeps the new PTRef + create for it a new index/literal
}

/*******************************************************************\

Function: smtcheck_opensmt2t_la::const_from_str

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
literalt smtcheck_opensmt2t_la::const_from_str(const char* num)
{
    PTRef rconst = lalogic->mkConst(num); // Can have a wrong conversion sometimes!
    return push_variable(rconst); // Keeps the new PTRef + create for it a new index/literal
}

/*******************************************************************\

Function: smtcheck_opensmt2t_la::mult_numbers

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef smtcheck_opensmt2t_la::mult_numbers(const exprt &expr, vec<PTRef> &args) 
{
    bool is_lin_op = isLinearOp(expr,args);
    #ifdef SMT_DEBUG
        assert(is_lin_op);
        ptl = lalogic->mkNumTimes(args);
    #else
        if (!is_lin_op)
        {
            PTRef ptl_uns = runsupported2var(expr);
            
            // Add new equation of an unknown function (acording to name)
            //PTRef var_eq = create_equation_for_unsupported(expr);
            //set_to_true(logic->mkEq(ptl_uns,var_eq)); // (= |hifrog::c::unsupported_op2var#0| (op operand0 operand1)) 
            // Remove - consider again only when we have UF with LIA works

            return ptl_uns;
        }

        // If linear op, try to create it
        PTRef ptl;
        try
        {
            ptl = lalogic->mkNumTimes(args);
        }
        catch (...)
        { /* We catch and give a nice error message if it is not in debug mode
                 To See the error run with the SMT_DEBUG define on
                 */
            PTRef ptl_uns = runsupported2var(expr);
            
            // Add new equation of an unknown function (acording to name)
            //PTRef var_eq = create_equation_for_unsupported(expr);
            //set_to_true(logic->mkEq(ptl_uns,var_eq)); // (= |hifrog::c::unsupported_op2var#0| (op operand0 operand1)) 
            // Remove - consider again only when we have UF with LIA works            

            return ptl_uns;
        }
    #endif

    return ptl;
}

/*******************************************************************\

Function: smtcheck_opensmt2t_la::div_numbers

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef smtcheck_opensmt2t_la::div_numbers(const exprt &expr, vec<PTRef> &args) 
{
    bool is_lin_op = isLinearOp(expr,args);
    bool is_of_legal_form2solver = lalogic->isNumTerm(args[0]) &&  logic->isConstant(args[1]);
    #ifdef SMT_DEBUG
        assert(is_lin_op);
        ptl = lalogic->mkNumDiv(args);
    #else
        if ((!is_lin_op) || (!is_of_legal_form2solver))
        {
            PTRef ptl_uns = runsupported2var(expr);

            // Add new equation of an unknown function (acording to name)
            //PTRef var_eq = create_equation_for_unsupported(expr);
            //set_to_true(logic->mkEq(ptl_uns,var_eq)); // (= |hifrog::c::unsupported_op2var#0| (op operand0 operand1)) 
            // Remove - consider again only when we have UF with LIA works            

            return ptl_uns;
        }

        // If linear op, try to create it
        PTRef ptl;
        try
        {
            ptl = lalogic->mkNumDiv(args);
        }
        catch (...)
        { /* We catch and give a nice error message if it is not in debug mode
                 To See the error run with the SMT_DEBUG define on
                 */
            PTRef ptl_uns = runsupported2var(expr);
                        
            // Add new equation of an unknown function (acording to name)
            //PTRef var_eq = create_equation_for_unsupported(expr);
            //set_to_true(logic->mkEq(ptl_uns,var_eq)); // (= |hifrog::c::unsupported_op2var#0| (op operand0 operand1)) 
            // Remove - consider again only when we have UF with LIA works            

            return ptl_uns;
        }
    #endif

    return ptl;
}

/*******************************************************************\

Function: smtcheck_opensmt2t_la::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
literalt smtcheck_opensmt2t_la::convert(const exprt &expr)
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
    if (_id==ID_code || expr.type().id()==ID_code) { //Init structs, arrays etc.
        
        l = lunsupported2var(expr);
        // NO support to this type

    } else if (_id==ID_address_of) {
        
        l = lunsupported2var(expr);
        // NO support to this type
     
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
        
    } else if ((_id == ID_typecast || _id == ID_floatbv_typecast) && expr.has_operands()) {
    #ifdef SMT_DEBUG
        bool is_const =(expr.operands())[0].is_constant(); // Will fail for assert(0) if code changed here not carefully!
        cout << "; IT IS A TYPECAST OF " << (is_const? "CONST " : "") << expr.type().id() << endl;
    #endif
        
        l = ltype_cast(expr);
        
    #ifdef SMT_DEBUG
        char* s = getPTermString(l);
        cout << "; (TYPE_CAST) For " << expr.id() << " Created OpenSMT2 formula " << s << endl;
        free(s);
    #endif
    } else if (_id == ID_typecast || _id == ID_floatbv_typecast) {
    #ifdef SMT_DEBUG
        cout << "EXIT WITH ERROR: operator does not yet supported in the LIA version (token: " << _id << ")" << endl;
        assert(false); // Need to take care of - typecast no operands
    #else
        l = lunsupported2var(expr);
        // TODO: write a better supoort here
    #endif
    } else if (_id == ID_abs) {
        
        l = labs(expr);
        
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
        forall_operands(it, expr)
        {
            assert(!is_cprover_rounding_mode_var(*it)); // KE: we remove this before! 
            if (is_div_wtrounding && i >= 2)
            {
            #ifdef SMT_DEBUG
                cout << "EXIT WITH ERROR: * and / operators with more than 2 arguments have no support yet in the LIA version (token: "
                                << _id << ")" << endl;
                assert(false); // No support yet for rounding operator
            #else
                is_no_support = true; // Will cause to over approx all
            #endif
            }
            else
            { 
                // All the rest of the operators
                literalt cl = convert(*it);
                PTRef cp = literals[cl.var_no()];
                assert(cp != PTRef_Undef);
                args.push(cp);
                i++; // Only if really add an item to mult/div inc the counter

#ifdef SMT_DEBUG
                char *s = logic->printTerm(cp);
                std::cout << "; On inner iteration " << i
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

        PTRef ptl;
        if (is_no_support) { // If we don't supposrt the operator due to more than 2 args
            ptl = runsupported2var(expr);
            
            // Add new equation of an unknown function (acording to name)
            //PTRef var_eq = create_equation_for_unsupported(expr);
            //set_to_true(logic->mkEq(ptl,var_eq)); // (= |hifrog::c::unsupported_op2var#0| (op operand0 operand1)) 
            // Remove - consider again only when we have UF with LIA works
        } else if (_id==ID_notequal) {
            ptl = logic->mkNot(logic->mkEq(args));
        } else if(_id == ID_equal) {
            ptl = logic->mkEq(args);
        } else if (_id==ID_if) {
            assert(args.size() >= 2); // KE: check the case if so and add the needed code!
            
            // If a then b, (without else) is a => b
            if (args.size() == 2)
            { 
                ptl = logic->mkImpl(args);
            } else {
                ptl = logic->mkIte(args);
                
#ifdef DISABLE_OPTIMIZATIONS
                if (dump_pre_queries)
                {
                    char *s = logic->printTerm(logic->getTopLevelIte(ptl));
                    ite_map_str.insert(make_pair(string(getPTermString(ptl)),std::string(s)));
                    //cout << "; XXX oite symbol: (" << ite_map_str.size() << ")" 
                    //    << string(getPTermString(ptl)) << endl << s << endl;
                    free(s); s=nullptr;   
                }
#endif
            }
        } else if(_id == ID_ifthenelse) {
            assert(args.size() >= 3); // KE: check the case if so and add the needed code!
            ptl = logic->mkIte(args);
            
#ifdef DISABLE_OPTIMIZATIONS
            if (dump_pre_queries)
            {
                char *s = logic->printTerm(logic->getTopLevelIte(ptl));
                ite_map_str.insert(make_pair(string(getPTermString(ptl)),std::string(s)));
                //cout << "; XXX oite symbol: (" << ite_map_str.size() << ")" 
                //        << string(getPTermString(ptl)) << endl << s << endl;
                free(s);    
            }
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
            assert(args.size() == 2); // KE: get errors before opensmt
            ptl = lalogic->mkNumGeq(args);
        } else if(_id == ID_le) {
            assert(args.size() == 2); // KE: get errors before opensmt
            ptl = lalogic->mkNumLeq(args);
        } else if(_id == ID_gt) {
            assert(args.size() == 2); // KE: get errors before opensmt 
            ptl = lalogic->mkNumGt(args);
        } else if(_id == ID_lt) {
            assert(args.size() == 2); // KE: get errors before opensmt
            ptl = lalogic->mkNumLt(args);
        } else if(_id == ID_plus) {
            ptl = lalogic->mkNumPlus(args);
        } else if(_id == ID_minus) {
            assert(args.size() == 2); // KE: check before opensmt, to locate better errors
            ptl = lalogic->mkNumMinus(args);
        } else if(_id == ID_unary_minus) {
            assert(args.size() == 1); // KE: check before opensmt, to locate better errors
            ptl = lalogic->mkNumMinus(args);
        } else if(_id == ID_unary_plus) {
            ptl = lalogic->mkNumPlus(args);
        } else if(_id == ID_mult) {
            ptl = mult_numbers(expr,args);
        } else if(_id == ID_div) {
            ptl = div_numbers(expr,args);
        } else if(_id == ID_assign) {
            ptl = logic->mkEq(args);
        } else if(_id == ID_ieee_float_equal) {
            ptl = logic->mkEq(args);
        } else if(_id == ID_ieee_float_notequal) {
            ptl = logic->mkNot(logic->mkEq(args));
        } else if(_id == ID_floatbv_plus) {
            ptl = lalogic->mkNumPlus(args);
        } else if(_id == ID_floatbv_minus) {
            assert(args.size() <= 2); // KE: check before opensmt, to locate better errors
            ptl = lalogic->mkNumMinus(args);
        } else if(_id == ID_floatbv_div) {
            ptl = div_numbers(expr,args);
        } else if(_id == ID_floatbv_mult) {
            ptl = mult_numbers(expr,args);
        } else if(_id == ID_index) {
#ifdef SMT_DEBUG
            std::cout << "EXIT WITH ERROR: Arrays and index of an array operators have no support yet in the LIA version (token: "
                            << _id << ")" << endl;
            assert(false); // No support yet for arrays
#else
            ptl = runsupported2var(expr);
                        
            // Add new equation of an unknown function (acording to name)
            //PTRef var_eq = create_equation_for_unsupported(expr);
            //set_to_true(logic->mkEq(ptl,var_eq)); // (= |hifrog::c::unsupported_op2var#0| (op operand0 operand1))
            // Remove - consider again only when we have UF with LIA works 
#endif
        } else if((_id == ID_address_of) || (_id == ID_pointer_offset)) {
#ifdef SMT_DEBUG
            std::cout << "EXIT WITH ERROR: Address and references of, operators have no support yet in the LIA version (token: "
                            << _id << ")" << endl;
            assert(false); // No support yet for address and pointers
#else
            ptl = runsupported2var(expr);
                                             
            // Add new equation of an unknown function (acording to name)
            //PTRef var_eq = create_equation_for_unsupported(expr);
            //set_to_true(logic->mkEq(ptl,var_eq)); // (= |hifrog::c::unsupported_op2var#0| (op operand0 operand1))
            // Remove - consider again only when we have UF with LIA works 
#endif
        } else if (_id == ID_pointer_object) {
#ifdef SMT_DEBUG
            std::cout << "EXIT WITH ERROR: Address and references of, operators have no support yet in the LIA version (token: "
                            << _id << ")" << endl;
            assert(false); // No support yet for pointers
#else
            ptl = runsupported2var(expr);
            // TODO: add UF equation to describe the inner part
#endif
        } else if (_id==ID_array) {
#ifdef SMT_DEBUG
            std::cout << "EXIT WITH ERROR: Arrays and index of an array operators have no support yet in the LIA version (token: "
                            << _id << ")" << endl;
            assert(false); // No support yet for arrays
#else
            bool is_need_constuction = ((converted_exprs.find(expr.hash()) == converted_exprs.end()));
            ptl = runsupported2var(expr);
            // TODO: add UF equation to describe the inner part
            
            if (is_need_constuction) {
                //std::cout << expr.pretty() << std::endl;
                // todo: ADD HERE SUPPORT FOR ARRAYS.
            }
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
            ptl = literals[lunsupported2var(expr).var_no()];
            // TODO
#endif            
        } else {
#ifdef SMT_DEBUG // KE - Remove assert if you wish to have debug info
            std::cout << _id << ";Don't really know how to deal with this operation:\n" << expr.pretty() << endl;
            std::cout << "EXIT WITH ERROR: operator does not yet supported in the LIA version (token: "
            		<< _id << ")" << endl;
            assert(false);
#else
            ptl = runsupported2var(expr);
            
            // Add new equation of an unknown function (acording to name)
            //PTRef var_eq = create_equation_for_unsupported(expr);
            //set_to_true(logic->mkEq(ptl,var_eq)); // (= |hifrog::c::unsupported_op2var#0| (op operand0 operand1)) 
            // Remove - consider again only when we have UF with LIA works
#endif
        }
        
        l = push_variable(ptl); // Keeps the new PTRef + create for it a new index/literal
    }
    converted_exprs[expr.hash()] = l;
#ifdef SMT_DEBUG
    PTRef ptr = literals[l.var_no()];
    char *s = logic->printTerm(ptr);
    std::cout << "; For " << _id << " Created OpenSMT2 formula " << s << endl;
    free(s); s=nullptr;
#endif
    return l;
}

/*******************************************************************\

Function: smtcheck_opensmt2t_la::runsupported2var

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef smtcheck_opensmt2t_la::runsupported2var(const exprt &expr) {
    if (converted_exprs.find(expr.hash()) != converted_exprs.end()) {
        literalt l = converted_exprs[expr.hash()];
        return literals[l.var_no()];
    }

    // Create a new unsupported var
    const std::string str = unsupported_info.create_new_unsupported_var(expr.type().id().c_str());
    
    PTRef var;
    if ((expr.is_boolean()) || (expr.type().id() == ID_c_bool)) 
        var = logic->mkBoolVar(str.c_str());
    else
        var = lalogic->mkNumVar(str.c_str());
   
    // Was taken from: literalt smtcheck_opensmt2t::store_new_unsupported_var
    // If need to register the abstracted functions - add it here
    store_new_unsupported_var(expr, var, false);

    return var;
}

/*******************************************************************\

Function: smtcheck_opensmt2t_la::lunsupported2var

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
literalt smtcheck_opensmt2t_la::lunsupported2var(const exprt &expr) 
{
    // Tries to map unsupported to another unsupported
    if (converted_exprs.find(expr.hash()) != converted_exprs.end())
        return converted_exprs[expr.hash()]; // TODO: might be buggy;

    // Create a new unsupported var
    const std::string str = unsupported_info.create_new_unsupported_var(expr.type().id().c_str());

    PTRef var;
    if ((expr.is_boolean()) || (expr.type().id() == ID_c_bool)) 
        var = logic->mkBoolVar(str.c_str());
    else
        var = lalogic->mkNumVar(str.c_str());
    
    return store_new_unsupported_var(expr, var);
}

/*******************************************************************\

Function: smtcheck_opensmt2t_la::evar

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef smtcheck_opensmt2t_la::evar(const exprt &expr, std::string var_name)
{
    assert(var_name.size() > 0);
    return ((expr.is_boolean()) || (expr.type().id() == ID_c_bool)) 
            ? logic->mkBoolVar(var_name.c_str()) : lalogic->mkNumVar(var_name.c_str());
}

/*******************************************************************\

Function: smtcheck_opensmt2t_la::lassert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
literalt smtcheck_opensmt2t_la::lassert(const exprt &expr)
{ 
    literalt lconstraints; 
    lconstraints = smtcheck_opensmt2t::push_variable(ptr_assert_var_constraints); 
    
    literalt l;
    l = land(convert(expr), lconstraints);
    return l;
}

/*******************************************************************\

Function: smtcheck_opensmt2t_la::create_constraints2type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
literalt smtcheck_opensmt2t_la::create_constraints2type(
		PTRef &var,
		std::string lower_b,
		std::string upper_b)
{
    vec<PTRef> args;
    vec<PTRef> args1; args1.push(lalogic->mkConst(lower_b.c_str())); args1.push(var);
    vec<PTRef> args2; args2.push(var); args2.push(lalogic->mkConst(upper_b.c_str()));
    PTRef ptl1 = lalogic->mkNumLeq(args1);
    PTRef ptl2 = lalogic->mkNumLeq(args2);
    literalt l1 = push_variable(ptl1);
    literalt l2 = push_variable(ptl2);

    return land(l1,l2);
}

/*******************************************************************\

Function: smtcheck_opensmt2t_la::push_assumes2type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void smtcheck_opensmt2t_la::push_assumes2type(
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
    std::cout << "; For Assume Constraints Created OpenSMT2 formula " << s << endl;
    std::cout << "; For Bounds " << lower_b.c_str() << " and " << upper_b.c_str() << endl;
    free(s); s=nullptr;
#endif
}

/*******************************************************************\

Function: smtcheck_opensmt2t_la::push_asserts2type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void smtcheck_opensmt2t_la::push_asserts2type(
		PTRef &var,
		std::string lower_b,
		std::string upper_b)
{
    if (type_constraints_level < 2) return;

    // Else add the checks
    literalt l = create_constraints2type(var, lower_b, upper_b); 
    PTRef ptr = literals[l.var_no()];
    ptr_assert_var_constraints = logic->mkAnd(ptr_assert_var_constraints, ptr);

#ifdef SMT_DEBUG_VARS_BOUNDS
    char *s = logic->printTerm(ptr);
    std::cout << "; For Assert Constraints Created OpenSMT2 formula " << s << endl;
    std::cout << "; Pushed Formula For Bounds " << lower_b.c_str() << " and " << upper_b.c_str() << endl;
    free(s); s=nullptr;
#endif
}

/*******************************************************************\

Function: smtcheck_opensmt2t_la::push_constraints2type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
bool smtcheck_opensmt2t_la::push_constraints2type(
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

Function: smtcheck_opensmt2t_la::add_constraints2type

  Inputs:

 Outputs:

 Purpose: If the expression is a number adds constraints

\*******************************************************************/
void smtcheck_opensmt2t_la::add_constraints2type(const exprt &expr, PTRef& var)
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
    std::cout << "; For variable " << expr.get(ID_identifier) << " in partition " << partition_count
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

 Purpose: we cannot express x*x or nodet*nodet (any) in LIA - assure
          we are not trying to push such an expression to the solver
          In case we sent this to the solver we will get assertion
          violation!

\*******************************************************************/
bool smtcheck_opensmt2t_la::isLinearOp(const exprt &expr, vec<PTRef> &args) {
	// Must be true
	if (!expr.has_operands()) return true;
	if (expr.operands().size() < 2) return true;
	if (expr.operands()[0].is_constant()) return true;
	if (expr.operands()[1].is_constant()) return true;

	// Must be false if there is more than one var
	int count_var = 0;
	for (int i=0; i< args.size(); i++) {
            bool is_linear = (logic->isConstant(args[i]) || 
                                lalogic->isNumTerm(args[i]) || 
                                lalogic->isNumPlus(args[i]) || 
                                lalogic->isUF(args[i]));
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
bool smtcheck_opensmt2t_la::is_non_linear_operator(PTRef tr)
{
    if (!lalogic->isNumDiv(tr) && !lalogic->isNumTimes(tr))
        return false;
    
    // Get the original vars
    const Pterm& t = logic->getPterm(tr);
    if (t.size() < 2)
        return false;
    
    // If we have 2 or more, than we can check if all constant but one
    int count_var = 0;
    for (int i = 0; i < t.size(); i++) {
        if (!logic->isConstant(t[i]) && !lalogic->isNumConst(t[i]))
            count_var++;
    }
    
    return (count_var > 1);
}
