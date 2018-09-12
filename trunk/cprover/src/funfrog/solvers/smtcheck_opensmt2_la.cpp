/*******************************************************************\

Module: Wrapper for OpenSMT2. Based on satcheck_minisat.

\*******************************************************************/
#include "smtcheck_opensmt2_la.h"
#include <util/type.h>
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

Function: smtcheck_opensmt2t_la::numeric_constante

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef smtcheck_opensmt2t_la::numeric_constant(const exprt & expr)
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

    rconst = lalogic->mkConst(num.c_str()); // Can have a wrong conversion sometimes!
    assert(rconst != PTRef_Undef);
    return rconst;
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
            PTRef ptl_uns = unsupported_to_var(expr);
            
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
            PTRef ptl_uns = unsupported_to_var(expr);
            
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
            PTRef ptl_uns = unsupported_to_var(expr);

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
            PTRef ptl_uns = unsupported_to_var(expr);
                        
            // Add new equation of an unknown function (acording to name)
            //PTRef var_eq = create_equation_for_unsupported(expr);
            //set_to_true(logic->mkEq(ptl_uns,var_eq)); // (= |hifrog::c::unsupported_op2var#0| (op operand0 operand1)) 
            // Remove - consider again only when we have UF with LIA works            

            return ptl_uns;
        }
    #endif

    return ptl;
}

PTRef smtcheck_opensmt2t_la::new_num_var(const std::string & var_name){
    return lalogic->mkNumVar(var_name.c_str());
}

/*******************************************************************\

Function: smtcheck_opensmt2t_la::expression_to_ptref

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef smtcheck_opensmt2t_la::expression_to_ptref(const exprt & expr)
{
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
    #ifdef SMT_DEBUG
        bool is_const =(expr.operands())[0].is_constant(); // Will fail for assert(0) if code changed here not carefully!
        cout << "; IT IS A TYPECAST OF " << (is_const? "CONST " : "") << expr.type().id() << endl;
        char* s = getPTermString(l);
        cout << "; (TYPE_CAST) For " << expr.id() << " Created OpenSMT2 formula " << s << endl;
        free(s);
    #endif
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

        // Convert first the arguments
        vec<PTRef> args;
        get_function_args(expr, args);
        bool is_no_support = (is_div_wtrounding && args.size() > 2);
        
        // Convert the whole expression with args<>
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
                    free(s);
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
            ptref = lalogic->mkNumGeq(args);
        } else if(_id == ID_le) {
            assert(args.size() == 2); // KE: get errors before opensmt
            ptref = lalogic->mkNumLeq(args);
        } else if(_id == ID_gt) {
            assert(args.size() == 2); // KE: get errors before opensmt
            ptref = lalogic->mkNumGt(args);
        } else if(_id == ID_lt) {
            assert(args.size() == 2); // KE: get errors before opensmt
            ptref = lalogic->mkNumLt(args);
        } else if(_id == ID_plus) {
            ptref = lalogic->mkNumPlus(args);
        } else if(_id == ID_minus) {
            assert(args.size() == 2); // KE: check before opensmt, to locate better errors
            ptref = lalogic->mkNumMinus(args);
        } else if(_id == ID_unary_minus) {
            assert(args.size() == 1); // KE: check before opensmt, to locate better errors
            ptref = lalogic->mkNumMinus(args);
        } else if(_id == ID_unary_plus) {
            ptref = lalogic->mkNumPlus(args);
        } else if(_id == ID_mult) {
            ptref = mult_numbers(expr,args);
        } else if(_id == ID_div) {
            ptref = div_numbers(expr,args);
        } else if(_id == ID_assign) {
            ptref = logic->mkEq(args);
        } else if(_id == ID_ieee_float_equal) {
            ptref = logic->mkEq(args);
        } else if(_id == ID_ieee_float_notequal) {
            ptref = logic->mkNot(logic->mkEq(args));
        } else if(_id == ID_floatbv_plus) {
            ptref = lalogic->mkNumPlus(args);
        } else if(_id == ID_floatbv_minus) {
            assert(args.size() <= 2); // KE: check before opensmt, to locate better errors
            ptref = lalogic->mkNumMinus(args);
        } else if(_id == ID_floatbv_div) {
            ptref = div_numbers(expr,args);
        } else if(_id == ID_floatbv_mult) {
            ptref = mult_numbers(expr,args);
        } else if(_id == ID_index) {
#ifdef SMT_DEBUG
            std::cout << "EXIT WITH ERROR: Arrays and index of an array operators have no support yet in the LA version (token: "
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
            std::cout << "EXIT WITH ERROR: Address and references of, operators have no support yet in the LA version (token: "
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
            std::cout << "EXIT WITH ERROR: Address and references of, operators have no support yet in the LA version (token: "
                            << _id << ")" << endl;
            assert(false); // No support yet for pointers
#else
            ptref = unsupported_to_var(expr);
            // TODO: add UF equation to describe the inner part
#endif
        } else if (_id==ID_array) {
#ifdef SMT_DEBUG
            std::cout << "EXIT WITH ERROR: Arrays and index of an array operators have no support yet in the LA version (token: "
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
            std::cout << _id << ";Don't really know how to deal with this operation:\n" << expr.pretty() << std::endl;
            std::cout << "EXIT WITH ERROR: operator does not yet supported in the LA version (token: "
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
#ifdef SMT_DEBUG
    char *s = logic->printTerm(ptref);
    std::cout << "; For " << _id << " Created OpenSMT2 formula " << s << endl;
    free(s);
#endif
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
PTRef smtcheck_opensmt2t_la::unsupported_to_var(const exprt &expr)
{
    auto it = unsupported_expr2ptrefMap.find(expr);
    if( it != unsupported_expr2ptrefMap.end()) { return it->second;}
    // Create a new unsupported var
    const std::string str = unsupported_info.create_new_unsupported_var(expr.type().id().c_str());

    const PTRef var = is_boolean(expr) ? logic->mkBoolVar(str.c_str()) : new_num_var(str);
    store_new_unsupported_var(expr, var); // for convert purpose only
    return var;
}


/*******************************************************************\

Function: smtcheck_opensmt2t_la::create_constraints2type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef smtcheck_opensmt2t_la::create_constraints2type(
        const PTRef var,
        std::string lower_b,
        std::string upper_b)
{
    vec<PTRef> args;
    vec<PTRef> args1; args1.push(lalogic->mkConst(lower_b.c_str())); args1.push(var);
    vec<PTRef> args2; args2.push(var); args2.push(lalogic->mkConst(upper_b.c_str()));
    PTRef ptl1 = lalogic->mkNumLeq(args1);
    PTRef ptl2 = lalogic->mkNumLeq(args2);

    return logic->mkAnd(ptl1, ptl2);
}

/*******************************************************************\

Function: smtcheck_opensmt2t_la::push_assumes2type

  Inputs:

 Outputs:

 Purpose: option 1,2

\*******************************************************************/
void smtcheck_opensmt2t_la::push_assumes2type(
        const PTRef var,
        std::string lower_b,
        std::string upper_b)
{
    if (type_constraints_level < 1 ) return;
    PTRef ptr = create_constraints2type(var, lower_b, upper_b);
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

 Purpose: option 2

\*******************************************************************/
void smtcheck_opensmt2t_la::push_asserts2type(
        const PTRef var,
        std::string lower_b,
        std::string upper_b)
{
    if (type_constraints_level < 2) return;

    // Else add the checks
    PTRef ptr = create_constraints2type(var, lower_b, upper_b);
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
        const PTRef var,
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
void smtcheck_opensmt2t_la::add_constraints2type(const exprt & expr, const PTRef var)
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
bool smtcheck_opensmt2t_la::is_non_linear_operator(PTRef tr) const
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

/*******************************************************************\

Function: smtcheck_opensmt2t_lra::abs_to_ptref

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef smtcheck_opensmt2t_la::abs_to_ptref(const exprt & expr)
{
    // ABS - all refers as real
    PTRef inner = expression_to_ptref((expr.operands())[0]); // Create the inner part
    PTRef ptl = logic->mkIte(
            lalogic->mkNumLt(inner, lalogic->getTerm_NumZero()),  // IF
            lalogic->mkNumNeg(inner),                 // Then
            inner);                                     // Else
#ifdef DISABLE_OPTIMIZATIONS
    if (dump_pre_queries)
    {
        char *s = logic->printTerm(logic->getTopLevelIte(ptl));
        ite_map_str.insert(make_pair(string(getPTermString(ptl)),std::string(s)));
        //cout << "; XXX oite symbol (labs):  (" << ite_map_str.size() << ")"
        //            << string(getPTermString(ptl)) << endl << s << endl;
        free(s);
    }
#endif
    return ptl;
}

/*******************************************************************\
Function: smtcheck_opensmt2t_la::type_cast

  Inputs:

 Outputs:

 Purpose:
 *
\*******************************************************************/
PTRef smtcheck_opensmt2t_la::type_cast(const exprt & expr)
{
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
        // Cast from Boolean to Num - Add
        PTRef operand_ptref = expression_to_ptref((expr.operands())[0]); // Creating the Bool expression
        PTRef ptl = logic->mkIte(operand_ptref, lalogic->mkConst("1"), lalogic->mkConst("0"));
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
        // Cast from Num to Boolean - Add
        PTRef operand_ptref = expression_to_ptref((expr.operands())[0]); // Creating the Bool expression
        PTRef ptl = logic->mkNot(logic->mkEq(operand_ptref, lalogic->mkConst("0")));
        return ptl;
    } else { // All types of number to number, will take the inner value as the converted one
        return expression_to_ptref((expr.operands())[0]);
    }
}


/*******************************************************************\

Function: smtcheck_opensmt2t_la::get_and_clear_var_constraints

  Inputs:

 Outputs:

 Purpose: Free all inner objects

\*******************************************************************/
FlaRef smtcheck_opensmt2t_la::get_and_clear_var_constraints()
{
    auto res = ptref_to_flaref(ptr_assert_var_constraints);
    ptr_assert_var_constraints = logic->getTerm_true();
    return res;
}