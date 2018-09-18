#include "smtcheck_z3_lra.h"

#include <util/std_expr.h>
#include <util/type.h>
#include <funfrog/utils/naming_helpers.h>
#include "../utils/naming_helpers.h"


/*******************************************************************\

Function: smtcheck_z3_lrat::initialize_solver

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void smtcheck_z3_lrat::initialize_solver()
{
    m_ptr_assert_var_constraints = new z3::expr(m_query_context.bool_val(true));
}

FlaRef smtcheck_z3_lrat::get_and_clear_var_constraints()
{
    FlaRef lconstraints; 
    lconstraints = smtcheck_z3t::push_variable(*m_ptr_assert_var_constraints);
    m_ptr_assert_var_constraints = new z3::expr(m_query_context.bool_val(true));
    
    return lconstraints;
}

/*******************************************************************\

Function: smtcheck_z3_lrat::evar

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
z3::expr smtcheck_z3_lrat::evar(const exprt &expr, std::string var_name)
{   
    assert(var_name.size() > 0);
    return((expr.is_boolean()) || (expr.type().id() == ID_c_bool)) ?
         m_query_context.bool_const(var_name.c_str()) :
         m_query_context.real_const(var_name.c_str()) ;
}

/*******************************************************************\

Function: smtcheck_z3_lrat::lconst_theory_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
z3::expr smtcheck_z3_lrat::numeric_constant(const exprt &expr)
{
    // Is it a Constant?
    assert ((expr.is_constant() && (expr.is_boolean() || is_number(expr.type()))) || (expr.type().id() == ID_pointer));
    
    // Get the data:
    std::string num = extract_expr_str_number(expr);

    // Can we convert it?
    assert((num.size() > 0) || (expr.type().id() == ID_c_enum) || (expr.type().id() == ID_c_enum_tag));
    
    // Convert it into a constant expression
    z3::expr rconst = (num.size() <= 0) 
        ? m_query_context.real_val((expr.type().id() == ID_c_enum) 
            ? expr.type().find(ID_tag).pretty().c_str()  // ID_c_enum
            : id2string(to_constant_expr(expr).get_value()).c_str()) // ID_c_enum_tag
        : m_query_context.real_val(num.c_str()); // General Case

    return rconst; // Keeps the new PTRef + create for it a new index/flaref
}

/*******************************************************************\

Function: smtcheck_z3_lrat::ltype_cast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
z3::expr smtcheck_z3_lrat::type_cast(const exprt &expr) {
    // KE: New Cprover code - patching
    bool is_expr_bool = (expr.is_boolean() || (expr.type().id() == ID_c_bool)); 
    bool is_operands_bool = ((expr.operands())[0].is_boolean() 
                || ((expr.operands())[0].type().id() == ID_c_bool)); 
    
    // KE: Take care of type cast - recursion of convert take care of it anyhow
    // Unless it is constant bool, that needs different code:
    if (expr.type().id() == (expr.operands())[0].type().id()) {
        // Skip - do the generic case
    } else if (is_expr_bool && (expr.operands())[0].is_constant()) {
    	std::string val = extract_expr_str_number((expr.operands())[0]);
    	return constant_bool(!((val.size()==0) || (stod(val)==0.0)));
    } else if (is_number(expr.type()) && is_operands_bool) {
    	// Cast from Boolean to Number - Add
    	z3::expr lt = expression_to_ptref((expr.operands())[0]); // Creating the Bool expression
        return z3::ite(!lt, m_query_context.real_val(0), m_query_context.real_val(1));        
    } else if (is_expr_bool && is_number((expr.operands())[0].type())) {
    	// Cast from Number to Boolean - Add
    	z3::expr a = expression_to_ptref((expr.operands())[0]); // Creating the Bool expression
        z3::expr b = m_query_context.real_val(0);
    	return !(a == b);
    }
    
    // Generic case:
    // OR else ignore casting (todo to check when it happens)
    return expression_to_ptref((expr.operands())[0]);
}

/*******************************************************************\

Function: smtcheck_z3_lrat::labs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
z3::expr smtcheck_z3_lrat::abs_to_ptref(const exprt &expr) 
{
    // ABS - all refers as real
    z3::expr lt = expression_to_ptref((expr.operands())[0]); // Create the inner part
    return z3::ite(lt < m_query_context.real_val(0), -lt, lt);
}

/*******************************************************************\

Function: smtcheck_z3_lrat::create_constraints2type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
z3::expr smtcheck_z3_lrat::create_constraints2type(
        const z3::expr var,
        std::string lower_b,
        std::string upper_b)
{
    z3::expr e = (m_query_context.real_val(lower_b.c_str()) <= var ) && (var <= m_query_context.real_val(upper_b.c_str())); 
    return e;
}