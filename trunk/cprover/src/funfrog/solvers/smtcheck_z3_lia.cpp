#include "smtcheck_z3_lia.h"

#include <util/type.h>
#include <util/mathematical_types.h>
#include <funfrog/utils/naming_helpers.h>
#include <funfrog/utils/string_utils.h>

/*******************************************************************\

Function: smtcheck_z3_liat::initialize_solver

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void smtcheck_z3_liat::initialize_solver()
{
    m_ptr_assert_var_constraints = new z3::expr(m_query_context.bool_val(true));
}

// lassert in non-incremental mode
FlaRef smtcheck_z3_liat::get_and_clear_var_constraints()
{
    FlaRef lconstraints; 
    lconstraints = smtcheck_z3t::push_variable(*m_ptr_assert_var_constraints);
    m_ptr_assert_var_constraints = new z3::expr(m_query_context.bool_val(true));
    
    return lconstraints;
}

/*******************************************************************\

Function: smtcheck_z3_liat::evar

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
z3::expr smtcheck_z3_liat::evar(const exprt &expr, std::string var_name)
{ 
    assert(var_name.size() > 0);
    return((expr.is_boolean()) || (expr.type().id() == ID_c_bool)) ?
         m_query_context.bool_const(var_name.c_str()) :
         m_query_context.int_const(var_name.c_str()) ;
}

/*******************************************************************\

Function: smtcheck_z3_liat::lconst_theory_type

  Inputs:

 Outputs:

 Purpose:

 * FIXME: Add 64/32 bit construction here
\*******************************************************************/
z3::expr smtcheck_z3_liat::numeric_constant(const exprt &expr)
{
    // Is it a Constant?
    assert ((expr.is_constant() && (expr.is_boolean() || is_number(expr.type()))) || (expr.type().id() == ID_pointer));
    
    // Get the data:
    std::string num = extract_expr_str_number(expr);

    // Can we convert it?
    assert((num.size() > 0) || (expr.type().id() == ID_c_enum) || (expr.type().id() == ID_c_enum_tag));
    
    // If not an Integer - replace with unsupported variable!
    if (!is_integer_string(num)) return unsupported_to_var(expr);
    
    // Convert it into a constant expression
    z3::expr rconst = m_query_context.int_val(std::to_string(stoi(num)).c_str()); // General Case

    return rconst; // Keeps the new PTRef + create for it a new index/flaref
}

/*******************************************************************\

Function: smtcheck_z3_liat::ltype_cast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
z3::expr smtcheck_z3_liat::type_cast(const exprt &expr) {
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
    	return z3::ite(!lt, m_query_context.int_val(0), m_query_context.int_val(1));
    } else if (is_expr_bool && is_number((expr.operands())[0].type())) {
    	// Cast from Number to Boolean - Add
    	z3::expr lt = expression_to_ptref((expr.operands())[0]); // Creating the Bool expression
    	return !(lt == 0);
    }
    
    // Generic case:
    // OR else ignore casting (todo to check when it happens)
    return expression_to_ptref((expr.operands())[0]);
}


/*******************************************************************\

Function: smtcheck_z3_liat::labs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
z3::expr smtcheck_z3_liat::abs_to_ptref(const exprt &expr) 
{
    // ABS - all refers as real
    z3::expr lt = expression_to_ptref((expr.operands())[0]); // Create the inner part
    return z3::ite(lt < 0, -lt, lt);
}

/*******************************************************************\

Function: smtcheck_z3_liat::create_constraints2type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
z3::expr smtcheck_z3_liat::create_constraints2type(
        const z3::expr var,
        std::string lower_b,
        std::string upper_b)
{
    z3::expr e = (m_query_context.int_val(lower_b.c_str()) <= var ) && (var <= m_query_context.int_val(upper_b.c_str())); 
    return e;
}