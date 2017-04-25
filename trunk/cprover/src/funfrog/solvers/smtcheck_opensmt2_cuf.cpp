/****logic***************************************************************\

Module: Wrapper for OpenSMT2. Based on satcheck_minisat.

Author: Grigory Fedyukovich

\*******************************************************************/
#include <queue>
#include <math.h>

#include "smtcheck_opensmt2_cuf.h"

//#define SMT_DEBUG
//#define DEBUG_SMT_BB
//#define DEBUG_SMT2SOLVER

void smtcheck_opensmt2t_cuf::initializeSolver(const char* name)
{
  osmt = new Opensmt(opensmt_logic::qf_cuf, name, bitwidth);
  logic = &(osmt->getCUFLogic());
  uflogic = &(osmt->getCUFLogic());
  bvlogic = &((BVLogic&)osmt->getLogic());
  mainSolver = &(osmt->getMainSolver());

  SolverId id = { 0 };
  vec<PtAsgn> asgns;
  vec<DedElem> deds;
  vec<PTRef> foo;
  bitblaster = new BitBlaster(id, osmt->getConfig(), *mainSolver, *bvlogic, asgns, deds, foo);

  const char* msg2=NULL;
  osmt->getConfig().setOption(SMTConfig::o_produce_inter, SMTOption(true), msg2);
  osmt->getConfig().setOption(SMTConfig::o_random_seed, SMTOption((int)get_random_seed()), msg2);
  //if (msg2 != NULL) { free((char *)msg2);}

  // KE: Fix a strange bug can be related to the fact we are pushing
  // a struct into std::vector and use [] before any push_back
  literals.push_back(PTRef());
  new_variable(); // Shall be location 0, i.e., [l.var_no()] is [0]
  literals[0] = logic->getTerm_true(); // Which is .x =0
  // KE: End of fix

  max_num = (mp_integer::ullong_t) (pow (2, bitwidth) - 1);
  
  // how the check is implemented in malloc.c in the GNU C Library (glibc)
  assert("Please re-run with bit-width parameter that is a pow of 2!" && ((bitwidth != 0) && !(bitwidth & (bitwidth - 1))));
}

// Free all inner objects
smtcheck_opensmt2t_cuf::~smtcheck_opensmt2t_cuf()
{
    // Shall/When need to: freeSolver() ?
}

PTRef smtcheck_opensmt2t_cuf::unsupported2var_bv(const exprt &expr)
{
    string str;
    
    // Tries to map unsupported to another unsupported
    if (converted_exprs.find(expr.hash()) != converted_exprs.end()) {
        literalt l = converted_exprs[expr.hash()]; // TODO: might be buggy
        PTRef ptrf = literals[l.var_no()];
        str = std::string(logic->printTerm(ptrf));
    } else {
        str = smtcheck_opensmt2t::_unsupported_var_str + std::to_string(unsupported2var++);
        str = quote_varname(str);
    }
#ifdef DEBUG_SMT_BB
        cout << "; IT IS AN UNSUPPORTED VAR " << str 
                << " of TYPE " << expr.type().id_string() << endl;
#endif   
        
    _fails_type_id = expr.type().id_string(); // KE: keep the reason for failing
    
    return get_bv_var(str.c_str());
}

PTRef smtcheck_opensmt2t_cuf::var_bv(const exprt &expr)
{
    const irep_idt &_id=expr.id(); // KE: gets the id once for performance
    assert(_id==ID_symbol || _id==ID_nondet_symbol); // Only for data types!!
    
   
    // Check if we suppose to have a support for this
    const irep_idt &type_id=expr.type().id_string();
    bool isSupported = !((type_id==ID_union) || 
                         (type_id==ID_struct) ||
                         (type_id==ID_range) ||
                         (type_id==ID_array) ||
                         (type_id==ID_pointer) ||
                         (type_id==ID_code) ||
                         (type_id==ID_class));
    
    if (isSupported)
        return get_bv_var(expr.get("identifier").c_str());
    else
        return unsupported2var_bv(expr);
}

PTRef smtcheck_opensmt2t_cuf::get_bv_var(const char* name)
{
    return bvlogic->mkBVNumVar(name);
}

PTRef smtcheck_opensmt2t_cuf::get_bv_const(const char* val)
{
    return bvlogic->mkBVConst(val);
}

void smtcheck_opensmt2t_cuf::set_equal_bv(PTRef l1, PTRef l2)
{
    current_partition->push(bvlogic->mkBVEq(l1, l2));
}

bool smtcheck_opensmt2t_cuf::convert_bv_eq_ite(const exprt &expr, PTRef& ptl)
{
    assert (expr.id() == ID_equal || expr.id() == ID_ieee_float_equal);
    
#ifdef DEBUG_SMT_BB
    cout << "; IT IS A EQ ITE " << expr.id() << endl;
#endif
    
    exprt sing;
    exprt ite;
    if (expr.operands()[0].id() == ID_if){
        ite = expr.operands()[0];
        sing = expr.operands()[1];
    } else if (expr.operands()[1].id() == ID_if){
        ite = expr.operands()[1];
        sing = expr.operands()[0];
    } else {
        return false;
    }
    exprt ite_guard = ite.operands()[0];
    exprt ite_tru_choice = ite.operands()[1];
    exprt ite_fls_choice = ite.operands()[2];

    PTRef sing_bv = convert_bv(sing);
    PTRef guard_bv = convert_bv(ite_guard);
    PTRef tru_eq = bvlogic->mkBVEq(sing_bv, convert_bv(ite_tru_choice));
    PTRef fls_eq = bvlogic->mkBVEq(sing_bv, convert_bv(ite_fls_choice));
    PTRef guard_tru = bvlogic->mkBVEq(guard_bv, get_bv_const("1"));
    PTRef guard_fls = bvlogic->mkBVEq(guard_bv, get_bv_const("0"));

    ptl = bvlogic->mkBVLor(
            bvlogic->mkBVLand(guard_tru, tru_eq),
            bvlogic->mkBVLand(guard_fls, fls_eq));
    return true;
}

PTRef smtcheck_opensmt2t_cuf::lconst_bv(const exprt &expr)
{
    assert(expr.is_constant()); // If not a constant then assert
    
#ifdef DEBUG_SMT_BB
    const irep_idt &type_id=expr.type().id_string(); // Check by type how to convert    
    std::cout << ";; Extract constant number : " << expr.print_number_2smt() << " Of Type "
            << type_id << std::endl;
#endif       
        
    std::string str = expr.print_number_2smt();
    int isFirstchSign = (str[0] == '-' || str[0] == '+')? 1 : 0;
    assert("Check support for new data-type in Const converstion." && str.size() != 0);
    
    if ((str.compare("inf") == 0) || (str.compare("-inf") == 0))
    {
        // No inf values in toy models!
        if ((bitwidth != 32) && (bitwidth != 64) && (bitwidth != 128)) {
            cout << "\nNo support for \"big\" (> " << bitwidth << " bit) integers so far.\n\n";
            exit(0);
        }

        // Else - unsupported!
        return unsupported2var_bv(expr); // stub for now
        
    } else if (!(std::all_of(str.begin() + isFirstchSign, str.end(), ::isdigit))) {
        std::cout << "Abstract " << str << std::endl;
        // E.g., floats - unsupported!
        return unsupported2var_bv(expr); // stub for now
        
    } else {
        // Check if fits
        mp_integer int_value=string2integer(str);
        if (int_value < -max_num || max_num < int_value)
        {
            cout << "\nNo support for \"big\" (> " << bitwidth << " bit) integers so far.\n\n";
            exit(0);
        } 
        
        // Create the constant as string in OpenSMT2
        return get_bv_const(str.c_str());
    }
}

// KE: Got here and this failed? Please use the debug print at the end of this
// code to know which case you need to add!
// If not? OpenSMT2 will crash with this error:
// hifrog: ../../src/common/Alloc.h:64: const T& RegionAllocator<T>::operator[]
//    (RegionAllocator<T>::Ref) const [with T = unsigned int; 
//     RegionAllocator<T>::Ref = unsigned int]: Assertion `r < sz' failed.
PTRef smtcheck_opensmt2t_cuf::type_cast_bv(const exprt &expr)
{
    const exprt &expr_op0 = (expr.operands())[0];
    const irep_idt &_id0=expr_op0.id();  // KE: gets the id once for performance
    assert(_id0 != ID_floatbv_typecast); // Type-cast of float - KE: show me that!
        
#ifdef DEBUG_SMT_BB
    std::cout << ";;; Start (TYPE_CAST) for " << expr.type().id() 
               << " to " << (expr_op0.type().id()) << std::endl;
#endif  

    /* For Operators - TYPE CAST OP AS SHL, =, or another TYPE_CAST */        
    // KE: New Cprover code - patching
    bool is_expr_bool = expr.is_boolean() || (expr.type().id() == ID_c_bool); 
        
    // KE: Take care of type cast - recursion of convert take care of it anyhow
    // Unless it is constant bool, that needs different code:
    if ((expr.id()== ID_typecast) && (_id0 == ID_typecast) 
            && (expr_op0.operands().size() == 1)) { // Recursive typecast  
        PTRef ptl = type_cast_bv(expr_op0);
        if (is_expr_bool && is_number(expr_op0.type())) {
            ptl = bvlogic->mkBVNot(bvlogic->mkBVEq(ptl, get_bv_const(0)));
        } 

#ifdef DEBUG_SMT_BB
        std::cout << ";;; Start (TYPE_CAST) for bv operator inner 0 " << expr.type().id() 
           << " to " << (expr.operands())[0].type().id() << " and again to " 
           << (expr_op0.operands())[0].type().id() << " to id " 
           << (expr.operands())[0].id() << " to inner id " 
           << (expr_op0.operands())[0].id() << std::endl;
#endif
        return ptl;   
    } else if ((expr.id()== ID_typecast) && (_id0 == ID_typecast)) {
        assert(0); // No arguments - KE: show me that!
    } else if (expr.type().id() == expr_op0.type().id()) {
        return convert_bv(expr_op0);
    } else if (is_expr_bool && expr_op0.is_constant()) {
        std::string val = extract_expr_str_number(expr_op0);
        bool val_const_zero = (val.size()==0) || (stod(val)==0.0);
#ifdef DEBUG_SMT_BB        
        std::cout << ";;; IS THIS ZERO? " << val_const_zero << std::endl;
#endif        
        return get_bv_const(val_const_zero? "0" : "1");       
    } else if (is_expr_bool && is_number(expr_op0.type())) {
        // Cast from Real to Boolean - Add

        return bvlogic->mkBVNot(bvlogic->mkBVEq(convert_bv(expr_op0), get_bv_const(0)));
    } else {
        //} else if (is_number(expr.type()) && is_operands_bool) {
        // Cast from Boolean to Real - Add
        // As bool is signedbv, then no need to do anything in BVP
        // Unify with the main case

	return convert_bv(expr_op0);
    }
}

PTRef smtcheck_opensmt2t_cuf::labs_bv(const exprt &expr) 
{
    const irep_idt &type_id = ((expr.operands())[0]).type().id();
    assert(type_id != ID_pointer); // TODO
    
    // ABS - all refers as real
    PTRef ptl_inner = convert_bv((expr.operands())[0]); // Create the inner part        
    if (type_id == ID_unsignedbv || type_id == ID_natural) 
    // Unsigned: no need to do something
        return ptl_inner;
    
    // If signed we need to do something :
    vec<PTRef> args;
    args.push(bvlogic->mkBVSlt(ptl_inner, this->get_bv_const(0))); // IF a
    args.push(bvlogic->mkBVNeg(ptl_inner)); // then b
    args.push(ptl_inner);    
    PTRef ptl = bvlogic->mkBVLand(
                    bvlogic->mkBVLor(bvlogic->mkBVNot(args[0]), args[1]),
                    bvlogic->mkBVLor(args[0], args[2])
                    ); 
    
#ifdef SMT_DEBUG
    char* s = getPTermString(l);
    cout << "; (ABS) For " << expr.id() << " Created OpenSMT2 formula " << s << endl;
    free(s);
#endif

    return ptl;
}


PTRef smtcheck_opensmt2t_cuf::convert_bv(const exprt &expr)
{
#ifdef DEBUG_SMT_BB
        std::cout << "Bit-blasting expression type " << expr.id() << " "
               << ((expr.id()==ID_symbol || expr.id()==ID_nondet_symbol) ?
                   expr.get("identifier") : "") << std::endl;
#endif
    
    const irep_idt &_id=expr.id(); // KE: gets the id once for performance
    
    PTRef ptl;
    if (_id==ID_code) {
        
        ptl = unsupported2var_bv(expr); // stub for now
        
    } else if (_id==ID_symbol || _id==ID_nondet_symbol) {
#ifdef DEBUG_SMT_BB
        cout << "; IT IS A VAR" << endl;
#endif
       ptl = var_bv(expr);
       
#ifdef DEBUG_SMT_BB
        char* s = logic->printTerm(ptl);
        cout << "; CREATE A VAR in OPENSMT2 " << s << " of type " << expr.type().id_string() << endl;
        free(s);
#endif
    } else if (_id == ID_typecast && expr.operands().size() == 1) {
#ifdef DEBUG_SMT_BB
        cout << "; IT IS A TYPE-CAST " << endl;
#endif           
        ptl = type_cast_bv(expr);
        
    } else if (_id == ID_typecast || _id == ID_floatbv_typecast) {
        // KE: TODO, don't know how to do it yet...
        ptl = unsupported2var_bv(expr); // stub for now
                
    } else if (_id==ID_constant) {
#ifdef DEBUG_SMT_BB
        cout << "; IT IS A CONSTANT " << endl;
#endif        
        ptl = lconst_bv(expr);
#ifdef DEBUG_SMT_BB
        char* s = logic->printTerm(ptl);
        cout << "; CREAT A CONSTANT in OPENSMT2 " << s << endl;
        free(s);
#endif          
        
    } else if (_id == ID_abs) {
    
        ptl = labs_bv(expr);
        
    } else if (_id == ID_string_constant) {
        
        ptl = unsupported2var_bv(expr); // stub for now  
     
    } else if (_id == ID_isnan) {
        
        ptl = unsupported2var_bv(expr); // stub for now  

    } else if (_id == ID_isinf) {
        
        ptl = unsupported2var_bv(expr); // stub for now  

    } else if (_id == ID_isfinite) {
        
        ptl = unsupported2var_bv(expr); // stub for now  
        
    } else if (_id == ID_isnormal) {
        
        ptl = unsupported2var_bv(expr); // stub for now  
         
    } else if (_id == ID_sign) { // for macro signbit
      
        ptl = unsupported2var_bv(expr); // stub for now 
        
    } else if (_id == ID_byte_extract_little_endian) {
        
        ptl = unsupported2var_bv(expr); // stub for now  
                  
    } else if (_id == ID_byte_update_little_endian) {
        
        ptl = unsupported2var_bv(expr); // stub for now  
                  
    } else if (_id == ID_address_of) {
        
        ptl = unsupported2var_bv(expr); // stub for now  

    } else if (_id == ID_with) {
        
        ptl = unsupported2var_bv(expr); // stub for now
        
    } else if (_id == ID_index) {
        
        ptl = unsupported2var_bv(expr); // stub for now

    } else if (_id == ID_array) {
        
        ptl = unsupported2var_bv(expr); // stub for now

    } else if (_id == ID_union) {
        
        ptl = unsupported2var_bv(expr); // stub for now
     
    } else if (_id==ID_struct) {  
        
        ptl = unsupported2var_bv(expr); // stub for now
    
    } else if (_id == ID_member) {
        
        ptl = unsupported2var_bv(expr); // stub for now
        
    } else if (_id == ID_member_name) {
        
        ptl = unsupported2var_bv(expr); // stub for now
        
    } else if (_id == ID_C_member_name) {
        
        ptl = unsupported2var_bv(expr); // stub for now
        
    } else if (_id == ID_dynamic_object) {
        
        ptl = unsupported2var_bv(expr); // stub for now
        
    } else if (_id == ID_pointer) {
        
        ptl = unsupported2var_bv(expr); // stub for now 
        // KE: when active, also change the code in lvar
         
    } else if (_id == ID_pointer_offset) {
        
        ptl = unsupported2var_bv(expr); // stub for now 
        // KE: when active, also change the code in lvar
        
    } else if (_id == ID_pointer_object) {
        
        ptl = unsupported2var_bv(expr); // stub for now 
        // KE: when active, also change the code in lvar
                                  
    } else if ((_id == ID_equal) ||
               (_id == ID_ieee_float_equal) || 
               (_id == ID_assign)) {
#ifdef DEBUG_SMT_BB
            cout << "; IT IS = " << endl;
#endif         
        if (!convert_bv_eq_ite (expr, ptl))
            ptl = bvlogic->mkBVEq(
                    convert_bv(expr.operands()[0]),
                    convert_bv(expr.operands()[1]));

    } else if (_id == ID_not) {
#ifdef DEBUG_SMT_BB
            cout << "; IT IS ! " << endl;
#endif
        ptl = bvlogic->mkBVNot(
                    convert_bv(expr.operands()[0]));

    } else if ((_id==ID_notequal) || 
               (_id == ID_ieee_float_notequal)) {
#ifdef DEBUG_SMT_BB
            cout << "; IT IS != " << endl;
#endif
        ptl = bvlogic->mkBVNot(
                    bvlogic->mkBVEq(convert_bv(expr.operands()[0]),
                                    convert_bv(expr.operands()[1])));
        
    } else if (_id == ID_mod) {
#ifdef DEBUG_SMT_BB
            cout << "; IT IS A MOD (%) " << endl;
#endif        
        ptl = bvlogic->mkBVMod(convert_bv(expr.operands()[0]),
                                    convert_bv(expr.operands()[1]));
    
    } else if ((_id == ID_div) || (_id == ID_floatbv_div)) {
#ifdef DEBUG_SMT_BB
            cout << "; IT IS A DIV " << endl;
#endif
        ptl = bvlogic->mkBVDiv(convert_bv(expr.operands()[0]),
                                    convert_bv(expr.operands()[1]));
    
    } else {

        // For all operators that can have more than 2 args
        vec<PTRef> args;
        int i = 0;
        forall_operands(it, expr)
        {
            PTRef cp = convert_bv(*it);
            assert(cp != PTRef_Undef);
            args.push(cp);

            i++;
        }

#ifdef DEBUG_SMT_BB
        cout << "; IT IS A " << _id.c_str() << endl;
#endif
        if (_id == ID_if) {
            if (args.size() == 2) {
                ptl = bvlogic->mkBVLor(bvlogic->mkBVNot(args[0]), args[1]); 
            } else if (args.size() == 3) {
                ptl = bvlogic->mkBVLand(
                    bvlogic->mkBVLor(bvlogic->mkBVNot(args[0]), args[1]),
                    bvlogic->mkBVLor(args[0], args[2])
                    ); 
            } else {
                assert(0);
            }
            //assert(0);
            // KE: isn't it like implies if inside expr?
            // GF: this should be handled by convert_bv_eq_ite.
            //     but if ID_if appears in any other type of expr than equality,
            //     then we should handle it in a somewhat way.   
        } else if (_id == ID_ifthenelse) {
            ptl = bvlogic->mkBVLand(
                    bvlogic->mkBVLor(bvlogic->mkBVNot(args[0]), args[1]),
                    bvlogic->mkBVLor(args[0], args[2])
                    ); 
            // GF: TODO
        } else if (_id ==  ID_implies) {
            ptl = bvlogic->mkBVLor(bvlogic->mkBVNot(args[0]), args[1]);
            
        } else if (_id ==  ID_and) {

            ptl = (args.size() > 2) ?
                split_exprs_bv(_id, args) : bvlogic->mkBVLand(args);

        } else if (_id ==  ID_or) {

            ptl = (args.size() > 2) ?
                split_exprs_bv(_id, args) : bvlogic->mkBVLor(args);
            
        } else if (_id ==  ID_bitand) {

            ptl = (args.size() > 2) ?
                split_exprs_bv(_id, args) : bvlogic->mkBVBwAnd(args);

        } else if (_id ==  ID_bitxor) {

            ptl = (args.size() > 2) ?
                split_exprs_bv(_id, args) : bvlogic->mkBVBwXor(args);

        } else if (_id ==  ID_bitor) {

            ptl = (args.size() > 2) ?
                split_exprs_bv(_id, args) : bvlogic->mkBVBwOr(args);

        } else if (_id == ID_bitnot) { // KE: not sure about it
        
            ptl = unsupported2var_bv(expr);
            
        } else if (_id == ID_shl) {
        
            ptl = (args.size() > 2) ?
                split_exprs_bv(_id, args) : bvlogic->mkBVLshift(args);
        
        } else if (_id == ID_shr) {
            
            assert(0); // KE: need example
            
        } else if (_id == ID_lshr) {
            
            ptl = (args.size() > 2) ?
                split_exprs_bv(_id, args) : bvlogic->mkBVLRshift(args); 
        
        } else if (_id == ID_ashr) {
            
            ptl = (args.size() > 2) ?
                split_exprs_bv(_id, args) : bvlogic->mkBVARshift(args);
            
        } else if (_id == ID_ge ||
                    _id ==  ID_le ||
                    _id ==  ID_gt ||
                    _id ==  ID_lt) {  
            // Signed/unsigend ops.
            const irep_idt &type_id = expr.type().id();
            assert(type_id != ID_pointer); // TODO

            bool is_unsigned = (type_id == ID_unsignedbv ||
                            type_id == ID_natural);

            if (_id == ID_ge) {
                ptl = (is_unsigned) ? 
                    bvlogic->mkBVUgeq(args) : bvlogic->mkBVSgeq(args);
            } else if (_id == ID_le) {
                ptl = (is_unsigned) ?
                    bvlogic->mkBVUleq(args) : bvlogic->mkBVSleq(args);
            } else if (_id == ID_gt) {
                ptl = (is_unsigned) ?
                    bvlogic->mkBVUgt(args) : bvlogic->mkBVSgt(args);
            } else if (_id == ID_lt) {
                ptl = (is_unsigned) ?
                    bvlogic->mkBVUlt(args) : bvlogic->mkBVSlt(args);
            } else {
                assert(0);
            } 
            
        } else if (_id == ID_plus ||
                    _id == ID_unary_plus ||
                    _id == ID_floatbv_plus) {
            ptl = (args.size() > 2) ?
                split_exprs_bv(_id, args) : bvlogic->mkBVPlus(args);
            
        } else if (_id == ID_minus ||
                    _id == ID_unary_minus || 
                    _id == ID_floatbv_minus) {
            
            ptl = (args.size() > 2) ?
                split_exprs_bv(_id, args) : bvlogic->mkBVMinus(args);
                
        } else if (_id == ID_mult ||
                    _id == ID_floatbv_mult) {
            
            ptl = (args.size() > 2) ?
                split_exprs_bv(_id, args) : bvlogic->mkBVTimes(args);
                
        } else {
            
            //GF: to continue...
            ptl = unsupported2var_bv(expr); // stub for now

        }
    }
    
#ifdef DEBUG_SMT_BB
    char *s = logic->printTerm(ptl);
    cout << "; For " << _id << " Created OpenSMT2 formula " << s << endl;
    free(s);
#endif
    
    return ptl;
}

PTRef smtcheck_opensmt2t_cuf::split_exprs_bv(irep_idt id, vec<PTRef>& args)
{
    vec<PTRef> args_current;
    args_current.push(args.last()); args.pop();
    args_current.push(args.last()); args.pop();
	
    // Do like convert
    PTRef ptl;
    if (id == ID_plus ||
        id == ID_unary_plus ||
        id == ID_floatbv_plus) {
  
        ptl = bvlogic->mkBVPlus(args_current);
  
    } else if (id == ID_minus ||
                id == ID_unary_minus || 
                id == ID_floatbv_minus) {
                    
        ptl = bvlogic->mkBVMinus(args_current);
        
    } else if (id == ID_mult || id == ID_floatbv_mult) { 
        
        ptl = bvlogic->mkBVTimes(args_current);
    
    } else if (id == ID_and) {

        ptl = bvlogic->mkBVLand(args_current);

    } else if (id == ID_or) {

        ptl = bvlogic->mkBVLor(args_current);
  
    } else if (id ==  ID_bitand) {

        ptl = bvlogic->mkBVBwAnd(args_current);

    } else if (id ==  ID_bitxor) {

        ptl = bvlogic->mkBVBwXor(args_current);
        
    } else if (id ==  ID_bitor) {

        ptl = bvlogic->mkBVBwOr(args_current);
        
    } else if (id == ID_shl) {

        ptl = bvlogic->mkBVLshift(args_current);

    } else if (id == ID_shr) {
            
            assert(0); // KE: need example
            
    } else if (id == ID_lshr) { // KE: not sure about shr

        ptl = bvlogic->mkBVLRshift(args_current); 
            
    } else if (id == ID_ashr) {

        ptl = bvlogic->mkBVARshift(args_current); 
                    
    } else {
        
        assert(0); // need to add the case!
    }

    // Recursive call and tail of the recursion
    if (args.size() > 0) 
    {
        args.push(ptl);
        return split_exprs_bv(id, args); // recursive call
    } else {
        //std::cout << "build " << logic->printTerm(ptl) << std::endl;
        return ptl; // tail
    }
}

/* Used for both - uf values and bit-blasted values */
exprt smtcheck_opensmt2t_cuf::get_value(const exprt &expr)
{
    PTRef ptrf;
    
    // Check if it was bit-blasted or else, check if in the cuf values
    bool is_expr_bb = (converted_bitblasted_exprs.find(expr.hash()) != converted_bitblasted_exprs.end()); // In use: bindBB and here
    bool is_expr_uf = (converted_exprs.find(expr.hash()) != converted_exprs.end());
    
    if (is_expr_bb || is_expr_uf) {
        if (is_expr_bb)
            ptrf = converted_bitblasted_exprs[expr.hash()];
        else {
            literalt l = converted_exprs[expr.hash()]; // TODO: might be buggy
            ptrf = literals[l.var_no()];
        }

#ifdef DEBUG_SMT_BB
        std::cout << "Getting value for " << logic->printTerm(ptrf) 
                << " which " << ((is_expr_bb)? "was bb" : "was not bb") 
                << std::endl;
#endif
        
        // Get the value of the PTRef
        if (is_expr_bb) {
            bitblaster->computeModel();
            ValPair v1 = bitblaster->getValue(ptrf);
            assert(v1.val != NULL);
            irep_idt value(v1.val);
            
            // Create the expr with it
            constant_exprt tmp = constant_exprt();
            tmp.set_value(value);

            return tmp;
        }
        else if (logic->isIteVar(ptrf)) // true/false - evaluation of a branching
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

literalt smtcheck_opensmt2t_cuf::const_var_Real(const exprt &expr)
{
    //TODO: Check this
    literalt l;
    string num = extract_expr_str_number(expr);
    PTRef rconst = PTRef_Undef;
    if (num.size() <= 0)
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

    rconst = uflogic->mkCUFConst(atoi(num.c_str())); // uflogic To avoid dynamic cast
    
    assert(rconst != PTRef_Undef);

    l = push_variable(rconst); // Keeps the new PTRef + create for it a new index/literal

    return l;
}

// KE: Got here and this failed? Please use the debug print at the end of this
// code to know which case you need to add!
// If not? OpenSMT2 will crash with this error:
// hifrog: ../../src/common/Alloc.h:64: const T& RegionAllocator<T>::operator[]
//    (RegionAllocator<T>::Ref) const [with T = unsigned int; 
//     RegionAllocator<T>::Ref = unsigned int]: Assertion `r < sz' failed.
literalt smtcheck_opensmt2t_cuf::type_cast(const exprt &expr) {
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
#ifdef SMT_DEBUG       
        std::cout << " IS THIS ZERO? :" << val_const_zero << std::endl;
#endif
        return const_var(!val_const_zero);
    } else if (is_number(expr.type()) && is_operands_bool) {
        // Cast from Boolean to Real - Add
        literalt lt = convert((expr.operands())[0]); // Creating the Bool expression
        PTRef ptl = logic->mkIte(literals[lt.var_no()], uflogic->mkCUFConst(1), uflogic->mkCUFConst(0));
        return push_variable(ptl); // Keeps the new literal + index it
    } else if (is_expr_bool && is_number((expr.operands())[0].type())) {
        // Cast from Real to Boolean - Add
        literalt lt = convert((expr.operands())[0]); // Creating the Bool expression
        // TODO: to cuf, look many locations!
        PTRef ptl = logic->mkNot(logic->mkEq(literals[lt.var_no()], uflogic->mkCUFConst(0)));
        return push_variable(ptl); // Keeps the new literal + index it
    } else {
        return convert((expr.operands())[0]);
    }
}

literalt smtcheck_opensmt2t_cuf::convert(const exprt &expr)
{
// GF: disabling hash for a while, since it leads to bugs at some particular cases,
//     e.g., for (= |goto_symex::guard#3| (< |c::f::a!0#7| 10))
//           and (= |goto_symex::guard#4| (< |c::f::a!0#11| 10))
//
//    if(converted_exprs.find(expr.hash()) != converted_exprs.end())
//        return converted_exprs[expr.hash()];

#ifdef SMT_DEBUG
    cout << "\n\n; ON PARTITION " << partition_count << " CONVERTING with " << expr.has_operands() << " operands "<< /*expr.pretty() << */ endl;
#endif

    const irep_idt &_id=expr.id(); // KE: gets the id once for performance
    
    /* Check which case it is */
    literalt l;
    if (_id==ID_code) {
        
        l = lunsupported2var(expr);
        
    } else if (_id==ID_symbol || _id==ID_nondet_symbol) {
#ifdef SMT_DEBUG
        cout << "; IT IS A VAR" << endl;
#endif
        l = lvar(expr);
    } else if (_id==ID_constant) {
#ifdef SMT_DEBUG
        cout << "; IT IS A CONSTANT " << endl;
#endif
        l = lconst(expr);
    } else if (_id==ID_typecast && expr.has_operands()) {
#ifdef SMT_DEBUG
        bool is_const =(expr.operands())[0].is_constant(); // Will fail for assert(0) if code changed here not carefully!
        cout << "; IT IS A TYPECAST OF " << (is_const? "CONST " : "") << expr.type().id() << endl;
#endif
        // KE: Take care of type cast - recursion of convert take care of it anyhow
        // Unless it is constant bool, that needs different code:
        l = type_cast(expr);
#ifdef SMT_DEBUG
    char* s = getPTermString(l);
    cout << "; (TYPE_CAST) For " << expr.id() << " Created OpenSMT2 formula " << s << endl;
    free(s);
#endif
    } else if (_id==ID_typecast || _id==ID_floatbv_typecast) {
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
        vec<PTRef> args;
        int i = 0;
        forall_operands(it, expr)
        {
            // KE: recursion in case the expr is not simple - shall be in a visitor
            if (id2string(it->get(ID_identifier)).find("__CPROVER_rounding_mode#")!=std::string::npos) {
                // Skip - we don't need the rounding variable for non-bv logics + assure it is always rounding thing
            } else { // All the rest of the operators
                literalt cl = convert(*it);
                PTRef cp = literals[cl.var_no()];
                assert(cp != PTRef_Undef);
                args.push(cp);
#ifdef DEBUG_SMT2SOLVER
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
                if ((*it).id()==ID_symbol || (*it).id()==ID_nondet_symbol) {
                    std::stringstream convert, convert2; // stringstream used for the conversion
                    convert << s; std::string str_expr1 = convert.str();
                    convert2 << "|" << (*it).get(ID_identifier) << "|"; std::string str_expr2 = convert2.str();
                    str_expr2.erase(std::remove(str_expr2.begin(),str_expr2.end(),'\\'),str_expr2.end());
                    if ((*it).id() == ID_nondet_symbol && str_expr2.find("nondet") == std::string::npos)
                        str_expr2 = str_expr2.replace(1,7, "symex::nondet");
                    assert(str_expr1.compare(str_expr2) == 0);
                }
                free(s);
#endif
            }
            i++;
        }

        PTRef ptl;
        if ((args.size() > 2) &&
            ((_id==ID_plus) ||
             (_id==ID_minus) ||
             (_id==ID_unary_minus) ||
             (_id==ID_unary_plus) ||
             (_id==ID_mult) ||
             (_id==ID_floatbv_plus) ||
             (_id==ID_floatbv_minus) ||
             (_id==ID_floatbv_mult) ||
             (_id==ID_and) ||
             (_id==ID_or) ||
             (_id==ID_bitand) ||
             (_id==ID_bitor) ||
             (_id==ID_bitxor) ||
             (_id==ID_ashr) ||   
             (_id==ID_lshr) ||
             (_id==ID_shr) ||
             (_id==ID_shl)
                ))
        {
            //std::cout << "Before build size of " << args.size() << " items " << std::endl;
            // KE:  patching code - check when it is fixed in OpenSMT2 and disable it here.
            ptl = split_exprs(expr.id(), args);
        } else if (_id==ID_notequal) {
            // TODO: to cuf, look many locations!
            ptl = logic->mkNot(logic->mkEq(args));
        } else if (_id == ID_equal) {
            ptl = logic->mkEq(args);
        } else if (_id==ID_if) {
            ptl = logic->mkIte(args);
#ifdef DEBUG_SMT2SOLVER
            ite_map_str.insert(make_pair(string(getPTermString(ptl)), logic->printTerm(logic->getTopLevelIte(ptl))));
#endif
        } else if (_id == ID_ifthenelse) {
            ptl = logic->mkIte(args);
#ifdef DEBUG_SMT2SOLVER
            ite_map_str.insert(make_pair(string(getPTermString(ptl)),logic->printTerm(logic->getTopLevelIte(ptl))));
#endif
        } else if (_id == ID_and) {
            // TODO: to cuf
            ptl = logic->mkAnd(args); 
        } else if (_id == ID_or) {
            // TODO: to cuf
            ptl = logic->mkOr(args);
        } else if (_id == ID_bitand) {
            ptl = uflogic->mkCUFBwAnd(args);
        } else if (_id == ID_bitxor) {
            ptl = uflogic->mkCUFBwXor(args); 
        } else if (_id == ID_bitor) {
            ptl = uflogic->mkCUFBwOr(args);  
        } else if (_id == ID_bitnot) { // KE: not sure about it
            ptl = literals[lunsupported2var(expr).var_no()];             
        } else if (_id == ID_not) {
            // TODO: to cuf, look many locations!
            ptl = uflogic->mkCUFNot(args);
        } else if (_id == ID_implies) {
            ptl = uflogic->mkImpl(args);
        } else if (_id == ID_ge) {
            // uflogic To avoid dynamic cast - till the end of this section            
            ptl = uflogic->mkCUFGeq(args);
        } else if (_id == ID_le) {
            ptl = uflogic->mkCUFLeq(args);
        } else if (_id == ID_gt) {
            ptl = uflogic->mkCUFGt(args);
        } else if (_id == ID_lt) {
            ptl = uflogic->mkCUFLt(args);
        } else if (_id == ID_plus) {
            ptl = uflogic->mkCUFPlus(args);
        } else if (_id==ID_minus) {
            ptl = uflogic->mkCUFMinus(args);
        } else if (_id==ID_unary_minus) {
            ptl = uflogic->mkCUFMinus(args);
        } else if (_id==ID_unary_plus) {
            ptl = uflogic->mkCUFPlus(args);
        } else if (_id==ID_mult) {
            ptl = uflogic->mkCUFTimes(args);
        } else if (_id==ID_div) {
            ptl = uflogic->mkCUFDiv(args);
        } else if (_id==ID_mod) {
            ptl = uflogic->mkCUFMod(args);
        } else if (_id==ID_assign) {
            ptl = logic->mkEq(args);
        } else if (_id==ID_ieee_float_equal) {
            ptl = logic->mkEq(args);
        } else if (_id==ID_ieee_float_notequal) {
            ptl = uflogic->mkCUFNeq(args);
        } else if (_id==ID_floatbv_plus) {
            ptl = uflogic->mkCUFPlus(args);
        } else if (_id==ID_floatbv_minus) {
            ptl = uflogic->mkCUFMinus(args);
        } else if (_id==ID_floatbv_div) {
            ptl = uflogic->mkCUFDiv(args);
        } else if (_id==ID_floatbv_mult) {
            ptl = uflogic->mkCUFTimes(args);
        } else if (_id==ID_shl) {
            ptl = uflogic->mkCUFLshift(args);
        } else if (_id==ID_shr) { // KE: Not sure about shr
            ptl = uflogic->mkCUFLRshift(args); 
        } else if (_id==ID_lshr) {
            ptl = uflogic->mkCUFLRshift(args); 
        } else if (_id==ID_ashr) {
            ptl = uflogic->mkCUFARshift(args);     
        } else if (_id==ID_byte_extract_little_endian) {
            ptl = literals[lunsupported2var(expr).var_no()];
            // KE: TODO                 
        } else if (_id==ID_byte_update_little_endian) {
            ptl = literals[lunsupported2var(expr).var_no()];
            // KE: TODO              
        } else if (_id == ID_address_of) {
            ptl = literals[lunsupported2var(expr).var_no()];
            // KE: TODO
        } else if (_id==ID_with) {
            ptl = literals[lunsupported2var(expr).var_no()];
            // KE: TODO            
        } else if (_id==ID_index) {
            ptl = literals[lunsupported2var(expr).var_no()];
            // KE: TODO
        } else if (_id==ID_array) {
            ptl = literals[lunsupported2var(expr).var_no()];
            // KE: TODO    
        } else if (_id==ID_union) {
            ptl = literals[lunsupported2var(expr).var_no()];
            // KE: TODO              
        } else if (_id==ID_struct) {
            ptl = literals[lunsupported2var(expr).var_no()];
            // KE: TODO                          
        } else if (_id==ID_member) {
            ptl = literals[lunsupported2var(expr).var_no()];
            // KE: TODO       
        } else if (_id==ID_member_name) {
            ptl = literals[lunsupported2var(expr).var_no()];
            // KE: TODO   
        } else if (_id==ID_C_member_name) {
            ptl = literals[lunsupported2var(expr).var_no()];
            // KE: TODO       
        } else if (_id==ID_pointer) {
            ptl =literals[lunsupported2var(expr).var_no()];
            // KE: when active, also change the code in lvar
        } else if (_id==ID_pointer_offset) {
            ptl =literals[lunsupported2var(expr).var_no()];
            // KE: when active, also change the code in lvar 
        } else if (_id==ID_pointer_object) {
            ptl =literals[lunsupported2var(expr).var_no()]; 
        } else if (_id==ID_dynamic_object) {
            ptl =literals[lunsupported2var(expr).var_no()]; 
        } else if (_id == ID_string_constant) {
            ptl =literals[lunsupported2var(expr).var_no()];   
        } else if (_id == ID_isnan) {
            ptl =literals[lunsupported2var(expr).var_no()];   
        } else if (_id == ID_isinf) {
            ptl =literals[lunsupported2var(expr).var_no()]; 
        } else if (_id == ID_isfinite) {
            ptl =literals[lunsupported2var(expr).var_no()];     
        } else if (_id == ID_isnormal) {
            ptl =literals[lunsupported2var(expr).var_no()]; 
        } else if (_id == ID_sign) { // for macro signbit
            ptl =literals[lunsupported2var(expr).var_no()];
        } else if (_id == ID_abs) { // Can't in UF
            ptl =literals[lunsupported2var(expr).var_no()];    
        } else {
            cout << "EXIT WITH ERROR: operator does not yet supported in the CUF version (token: "
                        << expr.id() << ")" << endl;
            assert(false); // KE: tell me if you get here!
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

PTRef smtcheck_opensmt2t_cuf::split_exprs(irep_idt id, vec<PTRef>& args)
{
    vec<PTRef> args_current;
    args_current.push(args.last()); args.pop();
    args_current.push(args.last()); args.pop();
	
    // Do like convert
    PTRef ptl;

    // Uflogic to avoid dynamic cast
    if (id == ID_plus) {
        ptl = uflogic->mkCUFPlus(args_current);
    } else if (id == ID_minus) {
        ptl = uflogic->mkCUFMinus(args_current);
    } else if (id == ID_unary_minus) {
        ptl = uflogic->mkCUFMinus(args_current);
    } else if (id == ID_unary_plus) {
        ptl = uflogic->mkCUFPlus(args_current);
    } else if (id == ID_mult) {
        ptl = uflogic->mkCUFTimes(args_current);
    } else if (id == ID_floatbv_plus) {
        ptl = uflogic->mkCUFPlus(args_current);
    } else if (id == ID_floatbv_minus) {
        ptl = uflogic->mkCUFMinus(args_current);
    } else if (id == ID_floatbv_mult) {
        ptl = uflogic->mkCUFTimes(args_current);
    } else if (id == ID_shl) {
        ptl = uflogic->mkCUFLshift(args_current);
    } else if (id == ID_shr) {
        ptl = uflogic->mkCUFLRshift(args_current); 
    } else if (id == ID_lshr) {
        ptl = uflogic->mkCUFLRshift(args_current); 
    } else if (id == ID_ashr) {
        ptl = uflogic->mkCUFARshift(args_current);   
    } else if (id == ID_and) {
        // TODO: to cuf
        ptl = logic->mkAnd(args_current); 
    } else if (id == ID_or) {
        // TODO: to cuf
        ptl = logic->mkOr(args_current);
    } else if (id == ID_bitand) {
        ptl = uflogic->mkCUFBwAnd(args_current);
    } else if (id == ID_bitxor) {
        ptl = uflogic->mkCUFBwXor(args_current); 
    } else if (id == ID_bitor) {
        ptl = uflogic->mkCUFBwOr(args_current);  
    } else {
        assert(0); // need to add the case!
    }

    // Recursive call and tail of the recursion
    if (args.size() > 0) 
    {
        args.push(ptl);
        return split_exprs(id, args); // recursive call
    } else {
        //std::cout << "build " << logic->printTerm(ptl) << std::endl;
        return ptl; // tail
    }
}

/*******************************************************************

 Function: smtcheck_opensmt2t_cuf::lunsupported2var

 Inputs:

 Outputs:

 Purpose: In CUF it is **only** for unsupported operators, for 
 *        unsupported data type please use: lnsupportedDatatype2var

\*******************************************************************/
literalt smtcheck_opensmt2t_cuf::lunsupported2var(exprt expr)
{
    // Tries to map unsupported to another unsupported
    if (converted_exprs.find(expr.hash()) != converted_exprs.end())
        return converted_exprs[expr.hash()]; // TODO: might be buggy;
    
    
    // Create a new unsupported var
    std::string str =smtcheck_opensmt2t::_unsupported_var_str + std::to_string(unsupported2var++);
    str = quote_varname(str);
    
    // Create the correct type in opensmt
    PTRef var;
    if (expr.is_boolean()) 
        var = logic->mkBoolVar(str.c_str());
    else if (expr.type().id() == ID_c_bool) 
        // KE: New Cprover code - patching
        var = logic->mkBoolVar((expr.get_string(ID_value)).c_str());
    else
        var = uflogic->mkCUFNumVar(str.c_str()); // create unsupported var for expression we don't support

    literalt l = push_variable(var);
    
#ifdef DEBUG_SMT_BB
        cout << "; IT IS AN UNSUPPORTED VAR " << str << endl;
#endif     
    
    return l;
}

literalt smtcheck_opensmt2t_cuf::lnotequal(literalt l1, literalt l2){
    vec<PTRef> args;
    PTRef pl1 = literals[l1.var_no()];
    PTRef pl2 = literals[l2.var_no()];
    args.push(pl1);
    args.push(pl2);
    PTRef ans = uflogic->mkCUFNeq(args); // uflogic to avoid dynamic cast
    return push_variable(ans); // Keeps the new PTRef + create for it a new index/literal
}

literalt smtcheck_opensmt2t_cuf::lvar(const exprt &expr)
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
    if(is_number(expr.type()))
        //TODO: Check this
        var = uflogic->mkCUFNumVar(str.c_str());//Main CufNumVar, for symbols
    else if (expr.is_boolean())
        var = logic->mkBoolVar(str.c_str());
    else if (expr.type().id() == ID_c_bool) 
    { // KE: New Cprover code - patching
        std::string num(expr.get_string(ID_value));
        var = logic->mkBoolVar(num.c_str());
    }
    else { // Is a function with index, array, pointer
#ifdef SMT_DEBUG
        cout << "EXIT WITH ERROR: Arrays and index of an array operator have no support yet in the UF version (token: "
             << expr.type().id() << ")" << endl;
        assert(false); // No support yet for arrays
#else
        literalt l_unsupported = lunsupported2var(expr);
        var = literals[l_unsupported.var_no()];
        
        return l_unsupported; // No need to push it again, so return here
#endif
    }

    literalt l = push_variable(var); // Keeps the new PTRef + create for it a new index/literal

#ifdef DEBUG_SMT2SOLVER
    std::string add_var = str + " () " + getVarData(var);
    if (var_set_str.end() == var_set_str.find(add_var)) {
        var_set_str.insert(add_var);
    }
#endif

    return l;
}

void smtcheck_opensmt2t_cuf::bindBB(const exprt& expr, PTRef pt1)
{
    if (bitblaster->isBound(pt1))
    {
#ifdef DEBUG_SMT_BB
        PTRef old_bv = bitblaster->getBoundPTRef(pt1);
        std::cout << " -- Term " << logic->printTerm(pt1) << " is already refined with "
              << logic->printTerm(old_bv) << " and so we skip " << std::endl;
#endif
    } else {
        PTRef expr_bv = convert_bv(expr);

#ifdef DEBUG_SMT_BB
  std::cout << " -- Bind terms " << logic->printTerm(pt1) << " and "
          << logic->printTerm(expr_bv) << std::endl;
#endif

        bitblaster->bindCUFToBV(pt1, expr_bv); // (PTRef cuf_tr, PTRef bv_tr)
        converted_bitblasted_exprs[expr.hash()] = expr_bv;
  }
}

int smtcheck_opensmt2t_cuf::check_ce(std::vector<exprt>& exprs, std::map<const exprt, int>& model,
       std::set<int>& refined, std::set<int>& weak, int start, int end, int step, int do_dep)
{
    assert(step == -1 || step == 1);
    assert((step == 1) == (end - start >= 0));

#ifdef DEBUG_SMT_BB
    cout << "Check CE for " <<exprs.size() << " terms " << std::endl;
#endif

    std::set<exprt> encoded_vars;

    for (int i = start; i != end; i = i + step){

        if (refined.find(i) != refined.end()) continue;

        std::set<exprt> cur_vars;
        getVarsInExpr(exprs[i], cur_vars);

        // encode only the necessary part of the counter-example here
        for (auto it = cur_vars.begin(); it != cur_vars.end(); ++it)
        {
            if (encoded_vars.find(*it) != encoded_vars.end()) continue;

#ifdef DEBUG_SMT_BB
            if (model.find(*it) == model.end()) {
                cout << "No model for " << it->get("identifier") << "\n";
                assert(0);
            }
#endif
            PTRef ce_term = bvlogic->mkBVEq(convert_bv(*it), 
                    get_bv_const(std::to_string(model[*it]).c_str())); // KE: not sure what to do here!
            BVRef tmp;
            bitblaster->insertEq(ce_term, tmp);
            encoded_vars.insert(*it);
#ifdef DEBUG_SMT_BB
            cout <<  "  CE value: " << logic->printTerm(ce_term) << endl;
#endif
        }

        // encode the CUF-expression we want to validate w.r.t. the CE

        PTRef lp = convert_bv(exprs[i]);

#ifdef DEBUG_SMT_BB
            cout <<  "  Validating: [" << i << "]: " << logic->printTerm(lp) << endl;
#endif
            
        BVRef tmp;
        if (bvlogic->isBVLor(lp)){
            bitblaster->insertOr(lp, tmp);
        } else if (bvlogic->isBVEq(lp)){
            bitblaster->insertEq(lp, tmp);
        } else if (bvlogic->isBVOne(lp)) {
#ifdef DEBUG_SMT_BB            
            cout << " " << (exprs[i]).pretty() << endl;
#endif
//            assert(0); // Probably true (as 0000..0001)
        } else if (bvlogic->isBVNUMConst(lp)) {
            assert(0); // TODO: check when can it happen
        } else {
            assert(0);
        }

        if (s_False == mainSolver->check()){
            weak.insert(i);

            // heuristic to get weak "candidates" based on dependency analysis
            if (do_dep == 1){
                std::set<exprt> dep_vars;
                getVarsInExpr(exprs[i], dep_vars);

                for (int j = i + step; j != end; j = j + step){

                    if (refined.find(j) != refined.end()) continue;

                    std::set<exprt> cur_vars;
                    getVarsInExpr(exprs[j], cur_vars);

                    bool res = true;

                    for (auto it = cur_vars.begin(); it != cur_vars.end(); ++it){
                        if (dep_vars.find(*it) != dep_vars.end()) {
                            res = false;
                            break;
                        }
                    }

                    if (res) continue;

                    for (auto it = cur_vars.begin(); it != cur_vars.end(); ++it){
                        dep_vars.insert(*it);
                    }

                    weak.insert(j);
#ifdef DEBUG_SMT_BB
                    cout << "Potentially weak statement encoding [" << j << "] found" << endl;
#endif
                }
            }
            return (i + step);
        }
    }

    return -1;
}

void smtcheck_opensmt2t_cuf::refine_ce_one_iter(std::vector<exprt>& exprs, int i)
{
    if (!exprs[i].has_operands() || exprs[i].operands().size() < 2){
        cout << "what should we do with it?" << endl;
        return;
    }

    // do binding for lhs

    const exprt lhs_expr = exprs[i].operands()[0];
    if(lhs_expr.id() == ID_symbol){
        PTRef lhs = literals[convert(lhs_expr).var_no()];
        bindBB(lhs_expr, lhs);
    }
    
    // keep binding for rhs

    std::set<exprt> se;
    getVarsInExpr(exprs[i].operands()[1], se);

    for (auto it = se.begin(); it != se.end(); ++it){
        PTRef rhs = literals[convert(*it).var_no()];
        bindBB(*it, rhs);
    }
    
    PTRef lp = convert_bv(exprs[i]);

#ifdef DEBUG_SMT_BB
    cout <<  "  Refining [" << i << "]: " << logic->printTerm(lp) << endl;
#endif

    BVRef tmp;
    if (bvlogic->isBVLor(lp)){
        bitblaster->insertOr(lp, tmp);
    } else if (bvlogic->isBVEq(lp)){
        bitblaster->insertEq(lp, tmp);
    } else if (bvlogic->isBVOne(lp)) {
        ; // No action
    } else {
//        assert(0);
    }
}

bool smtcheck_opensmt2t_cuf::refine_ce_solo(std::vector<exprt>& exprs, int i)
{
    refine_ce_one_iter(exprs, i);
    
#ifdef DEBUG_SMT_BB
    cout <<  "  Before Notify Equalities for " << exprs.size() << " Equalities" << endl;
#endif     
    bitblaster->notifyEqualities();

    return solve();
}

bool smtcheck_opensmt2t_cuf::refine_ce_mul(std::vector<exprt>& exprs, std::set<int>& is)
{
    bool res = true;
    for (auto it = is.begin(); it != is.end(); ++it){
        if (exprs.size() <= *it) continue;

        refine_ce_one_iter(exprs, *it);
        res = false;
    }

    if (res) return res;

#ifdef DEBUG_SMT_BB
    cout <<  "  Before Notify Equalities for " << exprs.size() << " Equalities" << endl;
#endif     
    bitblaster->notifyEqualities();

    return solve();
}

bool smtcheck_opensmt2t_cuf::force_refine_ce(std::vector<exprt>& exprs, std::set<int>& refined)
{
    for (unsigned int i = 0; i < exprs.size(); i++){
        if (refined.find(i) != refined.end()) continue;
        refine_ce_one_iter(exprs, i);
    }
    
#ifdef DEBUG_SMT_BB
    cout <<  "  Before Notify Equalities for " << exprs.size() << " Equalities" << endl;
#endif    
    bitblaster->notifyEqualities();

    return solve();
}
