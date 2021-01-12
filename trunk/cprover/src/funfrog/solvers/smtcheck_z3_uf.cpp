#include "smtcheck_z3_uf.h"

#include <opensmt/Vec.h>
#include "../utils/naming_helpers.h"
#include <util/mathematical_types.h>

const char* smtcheck_z3_uft::tk_sort_unumber = "U"; // Not to collide with the sort definitions in the solver
const char* smtcheck_z3_uft::tk_mult = "fU*";
const char* smtcheck_z3_uft::tk_div = "fU/";
const char* smtcheck_z3_uft::tk_plus = "fU+";
const char* smtcheck_z3_uft::tk_minus = "fU-";
const char* smtcheck_z3_uft::tk_lt = "fU<";
const char* smtcheck_z3_uft::tk_le = "fU<=";
const char* smtcheck_z3_uft::tk_gt = "fU>";
const char* smtcheck_z3_uft::tk_ge = "fU>=";
const char* smtcheck_z3_uft::tk_neg = "fU-";


/*******************************************************************\

Function: smtcheck_z3_uft::initialize_solver

  Inputs:

 Outputs:

 Purpose: to assure we work with QF_UF only

\*******************************************************************/
void smtcheck_z3_uft::initialize_solver()
{
    sort_unumber = new z3::sort(m_query_context.uninterpreted_sort(tk_sort_unumber));
}

z3::func_decl smtcheck_z3_uft::s_mult ()  { return z3::function(tk_mult, *sort_unumber, *sort_unumber, *sort_unumber);}
z3::func_decl smtcheck_z3_uft::s_div  ()  { return z3::function(tk_div, *sort_unumber, *sort_unumber, *sort_unumber);} // "fU/";
z3::func_decl smtcheck_z3_uft::s_plus ()  { return z3::function(tk_plus, *sort_unumber, *sort_unumber, *sort_unumber);} // "fU+";
z3::func_decl smtcheck_z3_uft::s_minus()  { return z3::function(tk_minus, *sort_unumber, *sort_unumber, *sort_unumber);} // "fU-";
z3::func_decl smtcheck_z3_uft::s_lt   ()  { return z3::function(tk_lt, *sort_unumber, *sort_unumber, m_query_context.bool_sort());} // "fU<";
z3::func_decl smtcheck_z3_uft::s_le   ()  { return z3::function(tk_le, *sort_unumber, *sort_unumber, m_query_context.bool_sort());} // "fU<=";
z3::func_decl smtcheck_z3_uft::s_gt   ()  { return z3::function(tk_gt, *sort_unumber, *sort_unumber, m_query_context.bool_sort());} // "fU>";
z3::func_decl smtcheck_z3_uft::s_ge   ()  { return z3::function(tk_ge, *sort_unumber, *sort_unumber, m_query_context.bool_sort());} // "fU>=";
z3::func_decl smtcheck_z3_uft::s_neg  ()  { return z3::function(tk_neg, *sort_unumber, *sort_unumber);} // "fU-";
z3::func_decl smtcheck_z3_uft::s_pos  ()  { return z3::function(tk_plus, *sort_unumber, *sort_unumber);} // "fU+";

/*******************************************************************\

Function: smtcheck_z3_uft::evar

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
z3::expr smtcheck_z3_uft::evar(const exprt &expr, std::string var_name)
{ 
    assert(var_name.size() > 0);
    return((expr.is_boolean()) || (expr.type().id() == ID_c_bool)) ?
         m_query_context.bool_const(var_name.c_str()) :
         m_query_context.constant(var_name.c_str(), *sort_unumber) ;
}

/*******************************************************************\

Function: smtcheck_z3_uft::lconst_number

  Inputs:

 Outputs:

 Purpose: unsuported in EUF, replace in some encoding

\*******************************************************************/
z3::expr smtcheck_z3_uft::numeric_constant(const exprt &expr)
{
    // Is it a Constant?
    assert (expr.is_constant());
        
    // Get the data:
    std::string num = extract_expr_str_number(expr);

    // Can we convert it?
    assert((num.size() > 0) || (expr.type().id() == ID_c_enum) || (expr.type().id() == ID_c_enum_tag));
    
    // Create it as a var, TODO: find a better way
    z3::expr rconst = evar(expr, num);
    return rconst; // Keeps the new PTRef + create for it a new index/flaref
}

/*******************************************************************\

Function: smtcheck_z3_uft::ltype_cast

  Inputs:

 Outputs:

 Purpose: Basic support for type cast

\*******************************************************************/
z3::expr smtcheck_z3_uft::type_cast(const exprt &expr) 
{
    // KE: Take care of type cast - recursion of convert take care of it anyhow
    if (expr.type().id() == (expr.operands())[0].type().id()) {
        // Skip - do the generic case
    } else if (((expr.is_boolean() || (expr.type().id() == ID_c_bool))) 
            && (expr.operands())[0].is_constant()) {
    	std::string val = extract_expr_str_number((expr.operands())[0]);
    	return constant_bool(!((val.size()==0) || (stod(val)==0.0)));
    } else if (is_number(expr.type()) && is_number(((expr.operands())[0]).type())) {
        // Skip - do the generic case
    } else {
        // Unsupported in EUF!
        return unsupported_to_var(expr);
    }
    
    // Generic case:
    // OR else ignore casting (todo to check when it happens)
    return expression_to_ptref((expr.operands())[0]);
}

/*******************************************************************\

Function: smtcheck_z3_uft::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
z3::expr smtcheck_z3_uft::convert(const exprt &expr)
{
    const irep_idt &_id=expr.id(); // KE: gets the id once for performance
    
    /* Check which case it is */
    if (_id==ID_code || expr.type().id()==ID_code) { //Init structs, arrays etc.
        
        return unsupported_to_var(expr);
        // No support this data type
     
    } else if (_id==ID_address_of) {
        
        return unsupported_to_var(expr);
        // NO support to this type
             
    } else if(_id==ID_symbol || _id==ID_nondet_symbol){

        return symbol_to_ptref(expr);
        
    } else if (_id==ID_constant) {
        
        return constant_to_ptref(expr);
        
    } else if ((_id == ID_typecast || _id == ID_floatbv_typecast) && expr.has_operands()) {
#ifdef SMT_DEBUG
        bool is_const =(expr.operands())[0].is_constant(); // Will fail for assert(0) if code changed here not carefully!
        cout << "; IT IS A TYPECAST OF " << (is_const? "CONST " : "") << expr.type().id() << endl;
#endif
        return type_cast(expr);
 
    } else if (_id == ID_typecast || _id == ID_floatbv_typecast) {

        return unsupported_to_var(expr);
        // TODO: write a better suport to this case

    } else {
        
#ifdef SMT_DEBUG
        cout << "; IT IS AN OPERATOR" << endl;
#endif
 
        // Convert Arguments:
        std::vector<z3::expr> args;
        bool is_expr_has_unsupported = get_function_args(expr, args);
        if (is_expr_has_unsupported)
            m_unsupported_info.unsupported_info_equations.push_back(expr); // Currently only for lattice refinement

        // Convert the main expression
        if (_id==ID_notequal) {
            assert(args.size() == 2);
            return  !(args[0] == args[1]);
          
        } else if(_id == ID_equal) {
            assert(args.size() == 2);
            return  (args[0] == args[1]);
            
        } else if ((_id==ID_if) && (args.size()==2)) {
            return  z3::implies(args[0], args[1]);
         
        } else if ((_id==ID_if) && (args.size()==3)) {
            return  z3::ite(args[0], args[1], args[2]);

        } else if (_id==ID_if) {
            assert(0);
            
        } else if(_id == ID_ifthenelse) {
            assert(args.size() == 3); // KE: check the case if so and add the needed code!
            return  z3::ite(args[0], args[1], args[2]); 
  
        } else if(_id == ID_not) {
            assert(args.size() == 1); 
            return  !args[0];
       
        } else if(_id == ID_unary_minus) {
            assert(args.size() == 1);
            return  s_neg()(args[0]);

        } else if(_id == ID_unary_plus) {
            assert(args.size() == 1);
            return  s_pos()(args[0]);
       
        } else if(_id == ID_ieee_float_notequal) {
            assert(args.size() == 2);
            return  !(args[0] == args[1]);
          
        } else if(_id == ID_ieee_float_equal) {
            assert(args.size() == 2);
            return  (args[0] == args[1]);

        } else if(_id == ID_assign) {
            assert(args.size() == 2);
            return  (args[0] == args[1]);           
                           
        } else if(_id == ID_implies) {
            assert(args.size() == 2);
            return  z3::implies(args[0], args[1]);
            
        } else if(_id == ID_ge) {
            assert(args.size() == 2);
            return  s_ge()(args[0],args[1]);
   
        } else if(_id == ID_le) {
            assert(args.size() == 2);
            return  s_le()(args[0],args[1]);
    
        } else if(_id == ID_gt) {
            assert(args.size() == 2);
            return  s_gt()(args[0],args[1]);
   
        } else if(_id == ID_lt) {
            assert(args.size() == 2);
            return  s_lt()(args[0],args[1]);
    
        } else if(_id == ID_floatbv_minus) {
            assert(args.size() == 2);
            return  s_minus()(args[0],args[1]);     
         
        } else if(_id == ID_minus) {
            assert(args.size() == 2);
            return  s_minus()(args[0],args[1]);  
   
        } else if(_id == ID_div) {
            assert(args.size() == 2);
            return  s_div()(args[0],args[1]); 

        } else if(_id == ID_floatbv_div) {
            assert(args.size() == 2);
            return  s_div()(args[0],args[1]); 
   
        } else if(_id == ID_floatbv_plus && args.size() == 1) {
            return  args[0];   
            
                     
        } else if(_id == ID_floatbv_plus && args.size() == 2) {
            return  s_plus()(args[0],args[1]);   
            
                    
        } else if(_id == ID_floatbv_plus) {
            assert(args.size() > 1);
            z3::expr ptl  = s_plus()(args[0],args[1]); 
            for (unsigned i = 2; i < args.size(); i++) {
               ptl = s_plus()(ptl,args[i]);
            }
            return ptl;

        } else if(_id == ID_plus && args.size() == 1) {
            return  args[0];   
              
        } else if(_id == ID_plus && args.size() == 2) {
            return  s_plus()(args[0],args[1]);   
           
        } else if(_id == ID_plus) {            
            assert(args.size() > 1);
            z3::expr ptl  = s_plus()(args[0],args[1]); 
            for (unsigned i = 2; i < args.size(); i++) {
               ptl = s_plus()(ptl,args[i]);
            } 
            return ptl;

        } else if(_id == ID_floatbv_mult && args.size() == 1) {
            return  args[0];   
                  
        } else if(_id == ID_floatbv_mult && args.size() == 2) {
            return  s_mult()(args[0],args[1]);   
                
        } else if(_id == ID_floatbv_mult) {
            assert(args.size() > 1);
            z3::expr ptl  = s_mult()(args[0],args[1]); 
            for (unsigned i = 2; i < args.size(); i++) {
               ptl = s_mult()(ptl,args[i]);
            }
            return ptl;
            
        } else if(_id == ID_mult && args.size() == 1) {
            return  args[0];   
                     
        } else if(_id == ID_mult && args.size() == 2) {
            return  s_mult()(args[0],args[1]);   
            
                        
        } else if(_id == ID_mult) {
            assert(args.size() > 1);
            z3::expr ptl  = s_mult()(args[0],args[1]); 
            for (unsigned i = 2; i < args.size(); i++) {
               ptl = s_mult()(ptl,args[i]);
            }
            return ptl;
        
        } else if(_id == ID_and && args.size() == 1) {
            return  args[0];   
        
        } else if(_id == ID_and && args.size() == 2) {
            return  (args[0] && args[1]);
  
        } else if(_id == ID_and) {
            assert(args.size() > 1);
            z3::expr ptl  = args[0] && args[1];
            for (unsigned i = 2; i < args.size(); i++) {
               ptl = (ptl && args[i]);
            }
            return ptl;

        } else if(_id == ID_or && args.size() == 1) {
            return  args[0];   
            
                
        } else if(_id == ID_or && args.size() == 2) {
            return  (args[0] || args[1]);
                 
        } else if(_id == ID_or) {
            assert(args.size() > 1);
            z3::expr ptl  = args[0] || args[1];
            for (unsigned i = 2; i < args.size(); i++) {
               ptl = (ptl || args[i]);
            }
            return ptl;
            
        } else if(_id == ID_xor && args.size() == 1) {
            return  args[0];   
      
        } else if(_id == ID_xor && args.size() == 2) {
            return  (args[0] || args[1]) && ((!args[0]) || (!args[1]));

        } else if(_id == ID_xor) {
            assert(args.size() > 1);
            z3::expr ptl  = (args[0] || args[1]) && ((!args[0]) || (!args[1]));
            for (unsigned i = 2; i < args.size(); i++) {
               ptl = (ptl || args[i]) && ((!ptl) || (!args[i]));
            }
            return ptl;
            
        } else if ((_id == ID_pointer_object) || 
                  (_id==ID_array) || 
                  (_id==ID_struct) ||
                  (_id==ID_union) ||
                  (_id==ID_range) ||
                  (_id==ID_pointer)) {

            return unsupported_to_var(expr);
             
        } else { // Unsupported!         
            // If shall store the equation, add UF functions to the encoding
            z3::expr l = unsupported_to_var(expr);
            
            // Add new equation of an unknown function (acording to name)
            z3::expr var_eq = create_unsupported_uf_call(expr);
            if (!var_eq.is_const()) {
                z3::expr ptl = l;
                z3::expr var_call = (ptl == var_eq);
                set_to_true(var_call); // (= |hifrog::c::unsupported_op2var#0| (op operand0 operand1))
                m_current_partition->push_back(var_call);
                //std::cout << ">>> Unsupported Op. " << _id.c_str() << " replaced with EUF function "
                //        << ptl.to_string() << " == " << var_eq.to_string() << std::endl;
            }
            
            return l;
        }
    }
}