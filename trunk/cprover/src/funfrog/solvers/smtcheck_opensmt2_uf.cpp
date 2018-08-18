/*******************************************************************\

Module: Wrapper for OpenSMT2. Based on satcheck_minisat.

Author: Grigory Fedyukovich

\*******************************************************************/

#include "smtcheck_opensmt2_uf.h"
#include <util/std_expr.h>
#include <funfrog/utils/naming_helpers.h>

// Debug flags of this class:
//#define SMT_DEBUG

const char* smtcheck_opensmt2t_uf::tk_sort_ureal = "Real";
const char* smtcheck_opensmt2t_uf::tk_mult = "*";
const char* smtcheck_opensmt2t_uf::tk_div = "/";
const char* smtcheck_opensmt2t_uf::tk_plus = "+";
const char* smtcheck_opensmt2t_uf::tk_minus = "-";
const char* smtcheck_opensmt2t_uf::tk_lt = "<";
const char* smtcheck_opensmt2t_uf::tk_le = "<=";
const char* smtcheck_opensmt2t_uf::tk_gt = ">";
const char* smtcheck_opensmt2t_uf::tk_ge = ">=";
const char* smtcheck_opensmt2t_uf::tk_neg = "-";

/*******************************************************************\

Function: smtcheck_opensmt2t_uf::initializeSolver

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void smtcheck_opensmt2t_uf::initializeSolver(const char* name)
{
  osmt = new Opensmt(opensmt_logic::qf_uf, name);
  logic = &(osmt->getLogic());
  mainSolver = &(osmt->getMainSolver());

  const char* msg2 = nullptr;
  osmt->getConfig().setOption(SMTConfig::o_produce_inter, SMTOption(true), msg2);
  assert(strcmp(msg2, "ok") == 0);

  //Initialize the stuff to fake UF
  //Create new sort UReal
  char* msg = nullptr;
  sort_ureal = logic->declareSort(tk_sort_ureal, &msg);

  vec<SRef> args;
  
  // One arg
  args.push(sort_ureal);
  s_neg = logic->declareFun(tk_neg, sort_ureal, args, &msg, true);
  
  // Two args
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

    // MB: to handle flattening done by CPROVER for plus and multiplication expressions
    // TODO: Ask Antti which property to set, noScoping, chainble, or pairwise
    splus.setNoScoping();
    smult.setNoScoping();
  
  //Declare relations
  s_lt = logic->declareFun(tk_lt, logic->getSort_bool(), args, &msg, true);
  s_le = logic->declareFun(tk_le, logic->getSort_bool(), args, &msg, true);
  s_gt = logic->declareFun(tk_gt, logic->getSort_bool(), args, &msg, true);
  s_ge = logic->declareFun(tk_ge, logic->getSort_bool(), args, &msg, true);

  if (msg != nullptr) free(msg);
}

/*******************************************************************\

Function: smtcheck_opensmt2t_uf::mkURealMult

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef
smtcheck_opensmt2t_uf::mkURealMult(vec<PTRef>& args)
{
    return mkFun(s_mult, args);
}

/*******************************************************************\

Function: smtcheck_opensmt2t_uf::mkURealDiv

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef
smtcheck_opensmt2t_uf::mkURealDiv(vec<PTRef>& args)
{
    return mkFun(s_div, args);
}

/*******************************************************************\

Function: smtcheck_opensmt2t_uf::mkURealPlus

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef
smtcheck_opensmt2t_uf::mkURealPlus(vec<PTRef>& args)
{
    return mkFun(s_plus, args);
}

/*******************************************************************\

Function: smtcheck_opensmt2t_uf::mkURealMinus

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef
smtcheck_opensmt2t_uf::mkURealMinus(vec<PTRef>& args)
{
    return mkFun(s_minus, args);
}

/*******************************************************************\

Function: smtcheck_opensmt2t_uf::mkURealLt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef
smtcheck_opensmt2t_uf::mkURealLt(vec<PTRef>& args)
{
    assert(args.size() == 2);
    return mkFun(s_lt, args);
}
  
/*******************************************************************\

Function: smtcheck_opensmt2t_uf::mkURealLe

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef
smtcheck_opensmt2t_uf::mkURealLe(vec<PTRef>& args)
{
    assert(args.size() == 2);
    return mkFun(s_le, args);
}

/*******************************************************************\

Function: smtcheck_opensmt2t_uf::mkURealGt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef
smtcheck_opensmt2t_uf::mkURealGt(vec<PTRef>& args)
{
    assert(args.size() == 2);
    return mkFun(s_gt, args);
}
    
/*******************************************************************\

Function: smtcheck_opensmt2t_uf::mkURealGe

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef
smtcheck_opensmt2t_uf::mkURealGe(vec<PTRef>& args)
{
    assert(args.size() == 2);
    return mkFun(s_ge, args);
}

/*******************************************************************\

Function: smtcheck_opensmt2t_uf::~smtcheck_opensmt2t_uf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
// Free all inner objects
smtcheck_opensmt2t_uf::~smtcheck_opensmt2t_uf()
{
    // Shall/When need to: freeSolver() ?
}

/*******************************************************************\

Function: smtcheck_opensmt2t_uf::numeric_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef smtcheck_opensmt2t_uf::numeric_constant(const exprt &expr)
{
    //TODO: Check this
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
    
    rconst = logic->mkConst(sort_ureal, num.c_str());
    assert(rconst != PTRef_Undef);
    return rconst;
}

/*******************************************************************\

Function: smtcheck_opensmt2t_uf::type_cast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef smtcheck_opensmt2t_uf::type_cast(const exprt & expr) {
    // KE: New Cprover code - patching
    bool is_expr_bool = (expr.is_boolean() || (expr.type().id() == ID_c_bool)); 
    bool is_operands_bool = ((expr.operands())[0].is_boolean() 
                || ((expr.operands())[0].type().id() == ID_c_bool)); 
    
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
    	PTRef op_ptref = expression_to_ptref((expr.operands())[0]); // Creating the Bool expression
        PTRef ptl = logic->mkIte(op_ptref, logic->mkConst(sort_ureal, "1"), logic->mkConst(sort_ureal, "0"));
        
#ifdef  DISABLE_OPTIMIZATIONS
        if (dump_pre_queries)
        {
            char *s = logic->printTerm(logic->getTopLevelIte(ptl));
            ite_map_str.insert(make_pair(string(getPTermString(ptl)),std::string(s)));
            //cout << "; XXX oite symbol (type-cast): (" << ite_map_str.size() << ")" 
            //    << string(getPTermString(ptl)) << endl << s << endl;
            free(s); s=NULL;            
        }
#endif          
    	return ptl;
    } else if (is_expr_bool && is_number((expr.operands())[0].type())) {
    	// Cast from Real to Boolean - Add
        PTRef op_ptref = expression_to_ptref((expr.operands())[0]); // Creating the Bool expression
    	PTRef ptl = logic->mkNot(logic->mkEq(op_ptref, logic->mkConst(sort_ureal, "0")));
    	return ptl;
    } else {
    	return expression_to_ptref((expr.operands())[0]);
    }
}

/*******************************************************************\

Function: smtcheck_opensmt2t_uf::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef smtcheck_opensmt2t_uf::expression_to_ptref(const exprt & expr)
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

    PTRef ptref = get_from_cache(expr);
    if(ptref != PTRef_Undef) { return ptref;}

    const irep_idt &_id=expr.id(); // KE: gets the id once for performance
    
    /* Check which case it is */
    if (_id==ID_code || expr.type().id()==ID_code) { //Init structs, arrays etc.
        
        ptref = unsupported_to_var(expr);
        // No support this data type
     
    } else if (_id==ID_address_of) {
        
        ptref = unsupported_to_var(expr);
        // NO support to this type
             
    } else if(_id==ID_symbol || _id==ID_nondet_symbol){
#ifdef SMT_DEBUG
        cout << "; IT IS A VAR" << endl;
#endif
        ptref = symbol_to_ptref(expr);
    } else if (_id==ID_constant) {
#ifdef SMT_DEBUG
        cout << "; IT IS A CONSTANT " << endl;
#endif
        ptref = constant_to_ptref(expr);
    } else if ((_id == ID_typecast || _id == ID_floatbv_typecast) && expr.has_operands()) {
#ifdef SMT_DEBUG
        bool is_const =(expr.operands())[0].is_constant(); // Will fail for assert(0) if code changed here not carefully!
        cout << "; IT IS A TYPECAST OF " << (is_const? "CONST " : "") << expr.type().id() << endl;
#endif
    // KE: Take care of type cast - recursion of convert take care of it anyhow
    // Unless it is constant bool, that needs different code:
    ptref = type_cast(expr);

#ifdef SMT_DEBUG
    char* s = getPTermString(l);
    cout << "; (TYPE_CAST) For " << expr.id() << " Created OpenSMT2 formula " << s << endl;
    free(s); s=NULL;
#endif  
    } else if (_id == ID_typecast || _id == ID_floatbv_typecast) {
#ifdef SMT_DEBUG
        cout << "EXIT WITH ERROR: operator does not yet supported in the QF_UF version (token: " << _id << ")" << endl;
        assert(false); // Need to take care of - typecast no operands
#else
        ptref = unsupported_to_var(expr);
        // TODO: write a better suport to this case
#endif
    } else {
#ifdef SMT_DEBUG
        cout << "; IT IS AN OPERATOR" << endl;
#endif
        vec<PTRef> args;
        int i = 0;
        for(auto const & operand : expr.operands())
        {	
            // KE: recursion in case the expr is not simple - shall be in a visitor
            if (is_cprover_rounding_mode_var(operand)) {
                // Skip - we don't need the rounding variable for non-bv logics + assure it is always rounding thing
            } else { // All the rest of the operators
                PTRef cp = expression_to_ptref(operand);
                assert(cp != PTRef_Undef);
                args.push(cp);
                i++; // Only if really add an item to mult/div inc the counter
            }
        }

        if (_id==ID_notequal) {
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
                
#ifdef          DISABLE_OPTIMIZATIONS
                if (dump_pre_queries)
                {
                    char *s = logic->printTerm(logic->getTopLevelIte(ptref));
                    ite_map_str.insert(make_pair(string(getPTermString(ptref)),std::string(s)));
                    free(s);
                }
#endif
            }
        } else if(_id == ID_ifthenelse) {
            assert(args.size() >= 3); // KE: check the case if so and add the needed code!
            
            ptref = logic->mkIte(args);
#ifdef      DISABLE_OPTIMIZATIONS
            if (dump_pre_queries)
            {
                char *s = logic->printTerm(logic->getTopLevelIte(ptref));
                ite_map_str.insert(make_pair(string(getPTermString(ptref)),std::string(s)));
                free(s);
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
            //ptref = logic->mkRealGeq(args);
            ptref = this->mkURealGe(args);
        } else if(_id == ID_le) {
            //ptref = logic->mkRealLeq(args);
            ptref = this->mkURealLe(args);
        } else if(_id == ID_gt) {
            //ptref = logic->mkRealGt(args);
            ptref = this->mkURealGt(args);
        } else if(_id == ID_lt) {
            //ptref = logic->mkRealLt(args);
            ptref = this->mkURealLt(args);
        } else if(_id == ID_plus) {
            //ptref = logic->mkRealPlus(args);
            ptref = this->mkURealPlus(args);
        } else if(_id == ID_minus) {
            //ptref = logic->mkRealMinus(args);
            ptref = this->mkURealMinus(args);
        } else if(_id == ID_unary_minus) {
            //ptref = logic->mkRealMinus(args);
            ptref = this->mkURealMinus(args);
        } else if(_id == ID_unary_plus) {
            //ptref = logic->mkRealPlus(args);
            ptref = this->mkURealPlus(args);
        } else if(_id == ID_mult) {
            //ptref = logic->mkRealTimes(args);
            ptref = this->mkURealMult(args);
        } else if(_id == ID_div) {
            //ptref = logic->mkRealDiv(args);
            ptref = this->mkURealDiv(args);
        } else if(_id == ID_assign) {
            ptref = logic->mkEq(args);
        } else if(_id == ID_ieee_float_equal) {
            ptref = logic->mkEq(args);
        } else if(_id == ID_ieee_float_notequal) {
            ptref = logic->mkNot(logic->mkEq(args));
        } else if(_id == ID_floatbv_plus) {
            //ptref = logic->mkRealPlus(args);
            ptref = this->mkURealPlus(args);
        } else if(_id == ID_floatbv_minus) {
            //ptref = logic->mkRealMinus(args);
            ptref = this->mkURealMinus(args);
        } else if(_id == ID_floatbv_div) {
            //ptref = logic->mkRealDiv(args);
            ptref = this->mkURealDiv(args);
        } else if(_id == ID_floatbv_mult) {
            //ptref = logic->mkRealTimes(args);
            ptref = this->mkURealMult(args);
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
        } else if(_id == ID_index) {
#ifdef SMT_DEBUG
            cout << "EXIT WITH ERROR: Arrays and index of an array operator have no support yet in the UF version (token: "
                << _id << ")" << endl;
            assert(false); // No support yet for arrays
#else
            ptref = unsupported_to_var(expr);
            
            // Add new equation of an unknown function (acording to name)
            PTRef var_eq = create_equation_for_unsupported(expr);
            set_to_true(logic->mkEq(ptref,var_eq)); // (= |hifrog::c::unsupported_op2var#0| (op operand0 operand1))
#endif
        } else if((_id == ID_address_of) || (_id == ID_pointer_offset)) {
#ifdef SMT_DEBUG
            cout << "EXIT WITH ERROR: Address and references of, operators have no support yet in the QF/UF version (token: "
                            << _id << ")" << endl;
            assert(false); // No support yet for arrays
#else
            ptref = unsupported_to_var(expr);
                      
            // Add new equation of an unknown function (acording to name)
            PTRef var_eq = create_equation_for_unsupported(expr);
            set_to_true(logic->mkEq(ptref,var_eq)); // (= |hifrog::c::unsupported_op2var#0| (op operand0 operand1))
#endif
        } else if ((_id == ID_pointer_object) || (_id==ID_array)) {
#ifdef SMT_DEBUG
            cout << "EXIT WITH ERROR: Address and references of, operators have no support yet in the QF/UF version (token: "
                            << _id << ")" << endl;
            assert(false); // No support yet for arrays
#else
            ptref = unsupported_to_var(expr);
            // TODO
#endif            
        } else {
#ifdef SMT_DEBUG // KE - Remove assert if you wish to have debug info
            cout << _id << ";Don't really know how to deal with this operation:\n" << expr.pretty() << endl;
            cout << "EXIT WITH ERROR: operator does not yet supported in the QF/UF version (token: "
            		<< _id << ")" << endl;
            assert(false);
#else
            ptref = unsupported_to_var(expr);
            
            // Add new equation of an unknown function (acording to name)
            PTRef var_eq = create_equation_for_unsupported(expr);
            push_variable(var_eq); // storing also this PTRef in literals
            set_to_true(logic->mkEq(ptref,var_eq)); // (= |hifrog::c::unsupported_op2var#0| (op operand0 operand1))
#endif
            // KE: Missing float op: ID_floatbv_sin, ID_floatbv_cos
            // Do we need them now?
        }
    }

#ifdef SMT_DEBUG
    char *s = logic->printTerm(ptref);
    std::cout << "; For " << _id << " Created OpenSMT2 formula " << s << std::endl;
    free(s);
#endif
    assert(ptref != PTRef_Undef);
    store_to_cache(expr, ptref);
    return ptref;
}

/*******************************************************************\

Function: smtcheck_opensmt2t_uf::unsupported_to_var

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef smtcheck_opensmt2t_uf::unsupported_to_var(const exprt & expr)
{
    auto it = unsupported_expr2ptrefMap.find(expr);
    if( it != unsupported_expr2ptrefMap.end()) { return it->second;}
    // Create a new unsupported var
    const std::string str = create_new_unsupported_var(expr.type().id().c_str());

    const PTRef var = is_boolean(expr) ? logic->mkBoolVar(str.c_str())
            : logic->mkVar(sort_ureal, str.c_str());
    store_new_unsupported_var(expr, var);
    return var;
}

/*******************************************************************\

Function: smtcheck_opensmt2t_uf::getStringSMTlibDatatype

  Inputs:

 Outputs:

 Purpose: Get the SMT-lib data type in UF

\*******************************************************************/
std::string smtcheck_opensmt2t_uf::getStringSMTlibDatatype(const typet& type)
{ 
    if ((type.id()==ID_bool) || (type.id() == ID_c_bool))
        return SMTConstants::SMT_BOOL;
    if (is_number(type))
        return SMTConstants::SMT_UREAL;

    return SMTConstants::SMT_UNKNOWN; // Shall not get here
}

/*******************************************************************\

Function: smtcheck_opensmt2t_uf::getSMTlibDatatype

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
SRef smtcheck_opensmt2t_uf::getSMTlibDatatype(const typet& type)
{ 
    if ((type.id()==ID_bool) || (type.id() == ID_c_bool))
        return logic->getSort_bool();//SMT_BOOL;
    if (is_number(type))
        return sort_ureal; //SMT_UREAL;

    throw std::logic_error("Unknown datatype encountered!");
}

// Check if a literal is non-linear in the solver side
bool smtcheck_opensmt2t_uf::is_non_linear_operator(PTRef tr)
{
    std::string symName{logic->getSymName(tr)};
    if(symName.find("uns_") != std::string::npos){
        return true;
    }
    SymRef sr = logic->getPterm(tr).symb(); 
    if ((sr != this->s_mult) &&  (sr != this->s_div))
        return false;
    
    // Get the original vars
    const Pterm& t = logic->getPterm(tr);
    if (t.size() < 2)
        return false;
    
    // If we have 2 or more, than we can check if all constant but one
    int count_var = 0;
    for (int i = 0; i < t.size(); i++) {
        if (!logic->isConstant(t[i]))
            count_var++;
    }
    
    return (count_var > 1);
}

PTRef smtcheck_opensmt2t_uf::new_num_var(const std::string & var_name) {
    return logic->mkVar(sort_ureal, var_name.c_str());
}
