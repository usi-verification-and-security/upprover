/*******************************************************************\

Module: Wrapper for OpenSMT2. Based on satcheck_minisat.

Author: Grigory Fedyukovich

\*******************************************************************/

#include "smtcheck_opensmt2_uf.h"
#include "../hifrog.h"
#include <std_expr.h>

// Debug flags of this class:
//#define SMT_DEBUG

const char* smtcheck_opensmt2t_uf::tk_sort_ureal = "UReal";
const char* smtcheck_opensmt2t_uf::tk_mult = "*";
const char* smtcheck_opensmt2t_uf::tk_div = "/";
const char* smtcheck_opensmt2t_uf::tk_plus = "+";
const char* smtcheck_opensmt2t_uf::tk_minus = "-";
const char* smtcheck_opensmt2t_uf::tk_lt = "<";
const char* smtcheck_opensmt2t_uf::tk_le = "<=";
const char* smtcheck_opensmt2t_uf::tk_gt = ">";
const char* smtcheck_opensmt2t_uf::tk_ge = ">=";

void smtcheck_opensmt2t_uf::initializeSolver(const char* name)
{
  osmt = new Opensmt(opensmt_logic::qf_uf, name);
  logic = &(osmt->getLogic());
  mainSolver = &(osmt->getMainSolver());

  const char* msg2=NULL;
  osmt->getConfig().setOption(SMTConfig::o_produce_inter, SMTOption(true), msg2);
  //if (msg2!=NULL) free((char *)msg2);

  // KE: Fix a strange bug can be related to the fact we are pushing
  // a struct into std::vector and use [] before any push_back
  literals.push_back(PTRef());
  literalt l = new_variable(); // Shall be location 0, i.e., [l.var_no()] is [0]
  literals[0] = logic->getTerm_true(); // Which is .x =0
  // KE: End of fix

  //Initialize the stuff to fake UF
  //Create new sort UReal
  char* msg=NULL;
  sort_ureal = logic->declareSort(tk_sort_ureal, &msg);

  vec<SRef> args;
  args.push(sort_ureal);
  args.push(sort_ureal);

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
//  MB: in UF we should not assume that these symbols are commutative!
//  smult.setCommutes();
//  sdiv.setCommutes();
//  splus.setCommutes();
//  sminus.setCommutes();
  
  //Declare relations
  s_lt = logic->declareFun(tk_lt, logic->getSort_bool(), args, &msg, true);
  s_le = logic->declareFun(tk_le, logic->getSort_bool(), args, &msg, true);
  s_gt = logic->declareFun(tk_gt, logic->getSort_bool(), args, &msg, true);
  s_ge = logic->declareFun(tk_ge, logic->getSort_bool(), args, &msg, true);

  if (msg!=NULL) free(msg);
}

PTRef
smtcheck_opensmt2t_uf::mkURealMult(vec<PTRef>& args)
{
    char *msg=NULL;
    PTRef ret = logic->mkFun(s_mult, args, &msg);
    if (msg != NULL) free(msg);
    return ret;
}
PTRef
smtcheck_opensmt2t_uf::mkURealDiv(vec<PTRef>& args)
{
    char *msg=NULL;
    PTRef ret = logic->mkFun(s_div, args, &msg);
    if (msg != NULL) free(msg);
    return ret;
}

PTRef
smtcheck_opensmt2t_uf::mkURealPlus(vec<PTRef>& args)
{
    char *msg=NULL;
    PTRef ret = logic->mkFun(s_plus, args, &msg);
    if (msg != NULL) free(msg);
    return ret;
}

PTRef
smtcheck_opensmt2t_uf::mkURealMinus(vec<PTRef>& args)
{
    char *msg=NULL;
    PTRef ret = logic->mkFun(s_minus, args, &msg);
    if (msg != NULL) free(msg);
    return ret;
}

PTRef
smtcheck_opensmt2t_uf::mkURealLt(vec<PTRef>& args)
{
    assert(args.size() == 2);
    char *msg=NULL;
    PTRef ret = logic->mkFun(s_lt, args, &msg);
    if (msg != NULL) free(msg);
    return ret;
}
    
PTRef
smtcheck_opensmt2t_uf::mkURealLe(vec<PTRef>& args)
{
    assert(args.size() == 2);
    char *msg=NULL;
    PTRef ret = logic->mkFun(s_le, args, &msg);
    if (msg != NULL) free(msg);
    return ret;
}

PTRef
smtcheck_opensmt2t_uf::mkURealGt(vec<PTRef>& args)
{
    assert(args.size() == 2);
    char *msg=NULL;
    PTRef ret = logic->mkFun(s_gt, args, &msg);
    if (msg != NULL) free(msg);
    return ret;
}
    
PTRef
smtcheck_opensmt2t_uf::mkURealGe(vec<PTRef>& args)
{
    assert(args.size() == 2);
    char *msg=NULL;
    PTRef ret = logic->mkFun(s_ge, args, &msg);
    if (msg != NULL) free(msg);
    return ret;
}

// Free all inner objects
smtcheck_opensmt2t_uf::~smtcheck_opensmt2t_uf()
{
    // Shall/When need to: freeSolver() ?
}

exprt smtcheck_opensmt2t_uf::get_value(const exprt &expr)
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
//            assert(0);
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

literalt smtcheck_opensmt2t_uf::const_var_Real(const exprt &expr)
{
    //TODO: Check this
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
    
    rconst = logic->mkConst(sort_ureal, num.c_str());
    assert(rconst != PTRef_Undef);

    return push_variable(rconst); // Keeps the new PTRef + create for it a new index/literal
}

literalt smtcheck_opensmt2t_uf::type_cast(const exprt &expr) {
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
        PTRef ptl = logic->mkIte(literals[lt.var_no()], logic->mkConst(sort_ureal, "1"), logic->mkConst(sort_ureal, "0"));
        
#ifdef  DISABLE_OPTIMIZATIONS
        if (dump_pre_queries)
            ite_map_str.insert(make_pair(string(getPTermString(ptl)),logic->printTerm(logic->getTopLevelIte(ptl))));
#endif          
    	return push_variable(ptl); // Keeps the new literal + index it
    } else if (is_expr_bool && is_number((expr.operands())[0].type())) {
    	// Cast from Real to Boolean - Add
    	literalt lt = convert((expr.operands())[0]); // Creating the Bool expression
    	PTRef ptl = logic->mkNot(logic->mkEq(literals[lt.var_no()], logic->mkConst(sort_ureal, "0")));
    	return push_variable(ptl); // Keeps the new literal + index it
    } else {
    	return convert((expr.operands())[0]);
    }
}

literalt smtcheck_opensmt2t_uf::convert(const exprt &expr)
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
    // KE: Take care of type cast - recursion of convert take care of it anyhow
    // Unless it is constant bool, that needs different code:
    l = type_cast(expr);

#ifdef SMT_DEBUG
    char* s = getPTermString(l);
    cout << "; (TYPE_CAST) For " << expr.id() << " Created OpenSMT2 formula " << s << endl;
    free(s);
#endif  
    } else if (_id == ID_typecast || _id == ID_floatbv_typecast) {
#ifdef SMT_DEBUG
        cout << "EXIT WITH ERROR: operator does not yet supported in the QF_UF version (token: " << _id << ")" << endl;
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
            if (is_cprover_rounding_mode_var(*it)) {
                // Skip - we don't need the rounding variable for non-bv logics + assure it is always rounding thing
            } else { // All the rest of the operators
                literalt cl = convert(*it);
                PTRef cp = literals[cl.var_no()];
                assert(cp != PTRef_Undef);
                args.push(cp);
                i++; // Only if really add an item to mult/div inc the counter
            }
        }

        PTRef ptl;
        if (_id==ID_notequal) {
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
#ifdef          DISABLE_OPTIMIZATIONS
                if (dump_pre_queries)
                    ite_map_str.insert(make_pair(string(getPTermString(ptl)),logic->printTerm(logic->getTopLevelIte(ptl))));
#endif
            }
        } else if(_id == ID_ifthenelse) {
            assert(args.size() >= 3); // KE: check the case if so and add the needed code!
            
            ptl = logic->mkIte(args);
#ifdef      DISABLE_OPTIMIZATIONS
            if (dump_pre_queries)
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
            //ptl = logic->mkRealGeq(args);
            ptl = this->mkURealGe(args);
        } else if(_id == ID_le) {
            //ptl = logic->mkRealLeq(args);
            ptl = this->mkURealLe(args);
        } else if(_id == ID_gt) {
            //ptl = logic->mkRealGt(args);
            ptl = this->mkURealGt(args);
        } else if(_id == ID_lt) {
            //ptl = logic->mkRealLt(args);
            ptl = this->mkURealLt(args);
        } else if(_id == ID_plus) {
            //ptl = logic->mkRealPlus(args);
            ptl = this->mkURealPlus(args);
        } else if(_id == ID_minus) {
            //ptl = logic->mkRealMinus(args);
            ptl = this->mkURealMinus(args);
        } else if(_id == ID_unary_minus) {
            //ptl = logic->mkRealMinus(args);
            ptl = this->mkURealMinus(args);
        } else if(_id == ID_unary_plus) {
            //ptl = logic->mkRealPlus(args);
            ptl = this->mkURealPlus(args);
        } else if(_id == ID_mult) {
            //ptl = logic->mkRealTimes(args);
            ptl = this->mkURealMult(args);
        } else if(_id == ID_div) {
            //ptl = logic->mkRealDiv(args);
            ptl = this->mkURealDiv(args);
        } else if(_id == ID_assign) {
            ptl = logic->mkEq(args);
        } else if(_id == ID_ieee_float_equal) {
            ptl = logic->mkEq(args);
        } else if(_id == ID_ieee_float_notequal) {
            ptl = logic->mkNot(logic->mkEq(args));
        } else if(_id == ID_floatbv_plus) {
            //ptl = logic->mkRealPlus(args);
            ptl = this->mkURealPlus(args);
        } else if(_id == ID_floatbv_minus) {
            //ptl = logic->mkRealMinus(args);
            ptl = this->mkURealMinus(args);
        } else if(_id == ID_floatbv_div) {
            //ptl = logic->mkRealDiv(args);
            ptl = this->mkURealDiv(args);
        } else if(_id == ID_floatbv_mult) {
            //ptl = logic->mkRealTimes(args);
            ptl = this->mkURealMult(args);
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
#endif
        } else if(_id == ID_index) {
#ifdef SMT_DEBUG
            cout << "EXIT WITH ERROR: Arrays and index of an array operator have no support yet in the UF version (token: "
                << _id << ")" << endl;
            assert(false); // No support yet for arrays
#else
            ptl = literals[lunsupported2var(expr).var_no()];
#endif
        } else if((_id == ID_address_of) || (_id == ID_pointer_object) 
                || (_id == ID_pointer_offset)) {
#ifdef SMT_DEBUG
            cout << "EXIT WITH ERROR: Address and references of, operators have no support yet in the QF/UF version (token: "
                            << _id << ")" << endl;
            assert(false); // No support yet for arrays
#else
            ptl = literals[lunsupported2var(expr).var_no()];
#endif
        } else {
#ifdef SMT_DEBUG // KE - Remove assert if you wish to have debug info
            cout << _id << ";Don't really know how to deal with this operation:\n" << expr.pretty() << endl;
            cout << "EXIT WITH ERROR: operator does not yet supported in the QF/UF version (token: "
            		<< _id << ")" << endl;
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
    cout << "; For " << _id << " Created OpenSMT2 formula " << s << endl;
    free(s);
#endif
    return l;
}

literalt smtcheck_opensmt2t_uf::lunsupported2var(const exprt &expr)
{
    // Tries to map unsupported to another unsupported
    if (converted_exprs.find(expr.hash()) != converted_exprs.end())
        return converted_exprs[expr.hash()]; // TODO: might be buggy;
    
    const string str = create_new_unsupported_var();
    
    PTRef var;
    if ((expr.is_boolean()) || (expr.type().id() == ID_c_bool)) 
        var = logic->mkBoolVar(str.c_str());
    else
        var = logic->mkVar(sort_ureal, str.c_str());

    return store_new_unsupported_var(expr, var);
}

literalt smtcheck_opensmt2t_uf::lnotequal(literalt l1, literalt l2){
    vec<PTRef> args;
    PTRef pl1 = literals[l1.var_no()];
    PTRef pl2 = literals[l2.var_no()];
    args.push(pl1);
    args.push(pl2);
    PTRef ans = logic->mkNot(logic->mkEq(args));
    return push_variable(ans); // Keeps the new PTRef + create for it a new index/literal
}

literalt smtcheck_opensmt2t_uf::lvar(const exprt &expr)
{
    string str = extract_expr_str_name(expr); // NOTE: any changes to name - please added it to general method!
    str = quote_varname(str);

    // Nil is a special case - don't create a var but a val of true
    if (str.compare(NIL) == 0) return const_var(true);

#ifdef SMT_DEBUG
	cout << "; (lvar) Create " << str << endl;
#endif

    // Else if it is really a var, continue and declare it!
    PTRef var;
    assert(str.size() > 0);
    if(is_number(expr.type()))
        //TODO: Check this
    	var = logic->mkVar(sort_ureal, str.c_str());
    else if ((expr.is_boolean()) || (expr.type().id() == ID_c_bool)) 
    	var = logic->mkBoolVar(str.c_str());
    else { // Is a function with index, array, pointer
#ifdef SMT_DEBUG
    	cout << "EXIT WITH ERROR: Arrays and index of an array operator have no support yet in the UF version (token: "
    			<< expr.type().id() << ")" << endl;
    	assert(false); // No support yet for arrays
#else
    	var = literals[lunsupported2var(expr).var_no()];
#endif
    }

    literalt l = push_variable(var); // Keeps the new PTRef + create for it a new index/literal

#ifdef DISABLE_OPTIMIZATIONS
    std::string add_var = str + " () " + getVarData(var);
    if (var_set_str.end() == var_set_str.find(add_var)) 
        var_set_str.insert(add_var);
#endif

    return l;
}

std::string smtcheck_opensmt2t_uf::getStringSMTlibDatatype(const exprt& expr)
{ 
    if ((expr.is_boolean()) || (expr.type().id() == ID_c_bool))
        return SMT_BOOL;
    if (is_number(expr.type()))
        return SMT_UREAL;

    return SMT_UNKNOWN; // Shall not get here 
}

SRef smtcheck_opensmt2t_uf::getSMTlibDatatype(const exprt& expr)
{ 
    if ((expr.is_boolean()) || (expr.type().id() == ID_c_bool))
        return logic->getSort_bool();//SMT_BOOL;
    if (is_number(expr.type()))
        return sort_ureal; //SMT_UREAL;
    throw std::logic_error("Unknown datatype encountered!");
    assert(0); // Shall not get here 
}
