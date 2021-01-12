#include "smtcheck_z3.h"

#include <string>
#include <sstream>

#include "../utils/expressions_utils.h"
#include "../utils/naming_helpers.h"
#include "../utils/string_utils.h"
#include "smt_itp_z3.h"
#include "solver_options.h"
#include <util/mathematical_types.h>

#ifdef DISABLE_OPTIMIZATIONS
#include <fstream>
using namespace std;

#include <iostream>
#endif
   
// Defualt C'tor
smtcheck_z3t::smtcheck_z3t(const solver_optionst _solver_options, std::string _logic) :
      m_solver(0),
      m_logic(_logic),
      m_current_partition(nullptr),         
      m_no_flarefs(0),
      m_no_flarefs_last_solved(0),
      m_pushed_formulas(0),
      m_unsupported_info(unsupported_operations_z3t(_solver_options.m_store_unsupported_info, this)),
      m_solver_options(_solver_options)
#ifdef DISABLE_OPTIMIZATIONS  
      ,
      m_dump_queries(_solver_options.m_dump_query),
      m_dump_pre_queries(_solver_options.m_dump_pre_query),
      m_base_dump_query_name("__query_z3_"+_solver_options.m_dump_query_name), // .smt2 file
      m_pre_queries_file_name("__pre_query_z3_"+_solver_options.m_dump_query_name), // .smt2 file 
      m_header_str("")
#endif  
{ 
    // Set the logic
    m_solver = new z3::solver(m_query_context, m_logic.c_str());
    
    // Set random seed
    set_random_seed(m_solver_options.m_random_seed);

}
    
smtcheck_z3t::~smtcheck_z3t()
{
    m_top_level_formulas.clear();
    assert(m_top_level_formulas.size() == 0);
    
    if (m_solver != nullptr) delete m_solver;
}

void smtcheck_z3t::set_random_seed(unsigned int i)
{
    z3::params p(m_query_context);
    p.set("random_seed", i);
    m_solver->set(p);
    
    std::cout << ">>(Z3) Set " << p << std::endl;
}

fle_part_idt smtcheck_z3t::new_partition()
{
    // Finish the previous partition if any
    if (!m_last_partition_closed && m_current_partition != nullptr)
        close_partition();
    
    m_current_partition = new std::vector<z3::expr>();

    // we are creating new partition which is not closed at the moment
    m_last_partition_closed = false;
    return m_partition_count++;
}

void smtcheck_z3t::close_partition()
{
    assert(!m_last_partition_closed);
    assert(m_current_partition != nullptr);
    
    z3::expr pand = (*m_current_partition)[0];
    for(unsigned int i = 1; i < (*m_current_partition).size(); ++i) {
        pand = pand && (*m_current_partition)[i];
    }

    m_top_level_formulas.push_back(pand);
    m_current_partition = nullptr;
}

FlaRef smtcheck_z3t::new_variable() {
    FlaRef l{m_no_flarefs, false};
    m_no_flarefs++;
    return l;
}

// Used to be m_literals
FlaRef smtcheck_z3t::push_variable(z3::expr ptl) {
    FlaRef l = new_variable();
    m_flaref2exprs.push_back(ptl); // Keeps the new literal + index it
    return l; // Return the literal after creating all ok - check if here with SMT_DEBUG flag
}

// For error trace
exprt smtcheck_z3t::get_value(const exprt &expr)
{
    if(m_expression_to_smt_map.find(expr) != m_expression_to_smt_map.end()) {
        z3::expr* ptref = (m_expression_to_smt_map.find(expr))->second;

        // Get the value of the PTRef
        if (ptref->is_bool()) //true only
        {
            if (ptref->bool_value() == Z3_L_TRUE) {
                return true_exprt();
            } else if (ptref->bool_value() == Z3_L_FALSE) {
                return false_exprt();
            } else {
                return nil_exprt();
            }
        }
        else if (ptref->is_var() || ptref->is_const()) // Constant value
        {
            z3::expr ptref_eval = m_solver->get_model().eval(*ptref);
            
            // Create the value
            irep_idt value = ptref_eval.to_string();

            // Create the expr with it
            constant_exprt tmp(value, expr.type());
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
        exprt tmp = expr;

        for(auto & operand : tmp.operands())
        {
            exprt tmp_op = get_value(operand);
            operand.swap(tmp_op);
        }

        return tmp;
    }    
}

// For error trace
bool smtcheck_z3t::is_assignment_true(FlaRef a) const
{
    if (a.is_true())
        return true;
    else if (a.is_false())
        return false;

    // Gets the expression from z3
    assert(a.no() < m_flaref2exprs.size());
    //z3::expr a_e = flaref_to_ptref(a);
    z3::expr ptref = m_flaref2exprs[a.no()];
    z3::expr a_e = (a.sign()) ? !ptref : ptref;
    
    // Check if it is 0 (false) or else true
    z3::expr a_eval = m_solver->get_model().eval(a_e);
    if (a_eval.is_bool())
        return  (a_eval.bool_value() == Z3_L_TRUE);
    if (a_eval.is_int())
        return (a_eval.get_numeral_int() != 0);
    if (a_eval.is_real())
        return (a_eval.get_decimal_string(2) != "0.0");
    
    assert(0);
}

bool smtcheck_z3t::solve() 
{   
    if (m_current_partition != nullptr) {
        close_partition();
    }
  
// No interpolant    
#ifdef PRODUCE_PROOF    
  m_ready_to_interpolate = false;
#endif
  
// Add current inc. text and dump the query
#ifdef DISABLE_OPTIMIZATIONS   
    if (m_dump_pre_queries) {
        ofstream out_smt;
        std::string file;
        file=m_pre_queries_file_name+"_"+std::to_string(get_unique_index())+".smt2";
        out_smt.open(file);
        
        out_smt << ";; Input param logic is: " << m_logic << endl;
        out_smt << m_header_str;
        for(unsigned int i = m_pushed_formulas; i < m_top_level_formulas.size(); ++i) {
            out_smt << "; XXX Partition: " << (m_top_level_formulas.size() - i - 1) << endl;
            if (m_solver_options.m_incremental_solver) out_smt << "(assert \n";
            out_smt << "    " << m_top_level_formulas[i].to_string() << endl;
            if (m_solver_options.m_incremental_solver) out_smt << ")" << endl;
        }
        out_smt << "(check-sat)\n" << endl;
        
        out_smt.close();
    }
#endif 
    // Try to add all top level formula as asserts to the solver
    try {
        if (m_solver_options.m_incremental_solver){
            // Add the top level formula
            for(unsigned int i = m_pushed_formulas; i < m_top_level_formulas.size(); ++i) {
                m_solver->push(); // Track point - incremental solving
                m_solver->add(m_top_level_formulas[i]);
            }
        } else {
            // Add the top level formula
            for(unsigned int i = 0; i < m_top_level_formulas.size(); ++i)
                m_solver->add(m_top_level_formulas[i]);
        }
    } catch (const z3::exception& e) { 
        std::cerr << ";; Error during push z3 formula" << e.msg();
        exit(0);
    }

// As is in the solver:
#ifdef DISABLE_OPTIMIZATIONS   
    if (m_dump_queries) {
        ofstream out_smt;
        std::string file;
        file=m_base_dump_query_name+"_"+std::to_string(get_unique_index())+".smt2";
        out_smt.open(file);
        
        out_smt << ";; Input param logic is: " << m_logic << endl;
        out_smt << ";; Solver logic in-use: " << endl;
        out_smt << m_solver->to_smt2() << endl;
        
        out_smt.close();
    }
#endif    

    // Keep the number of pushed formulas (anyhow)
    m_pushed_formulas = m_top_level_formulas.size(); 

    // Solve the current queries
    //std::cout << ";;; Checking encoding to Z3" << std::endl;
    Z3_error_code error = m_query_context.check_error();
    if (error != Z3_OK) {
        std::cout << ">> ERROR:  Z3 query context error, exit" << std::endl;
        exit(0);
    }
    
    std::cout << "*** Checking with Z3 ***" << std::endl;
    z3::check_result r = m_solver->check();

    // Inc. Mode Info.
    if ((m_no_flarefs_last_solved != 0) && (m_no_flarefs_last_solved < m_no_flarefs) && m_solver_options.m_incremental_solver)
        std::cout << ";; Using Z3 Incremental Mode with "
                  << (m_no_flarefs - m_no_flarefs_last_solved) << " additional terms "
                  << std::endl;
    m_no_flarefs_last_solved = m_no_flarefs;

    //std::cout << "*** Result with Z3 " << ((r == z3::unsat) ? "UNSAT" :  ((r == z3::sat) ? "SAT" : "ERROR")) << " ***" << std::endl;
    if (r == z3::sat) {  
#ifdef PRODUCE_PROOF    
        m_ready_to_interpolate = true; // Only for SAT case
#endif        
        return true;
    } else if (r == z3::unsat) {
        return false;
    } else {
        std::cout << ";; Unknown result from solver Z3. " << std::endl;
        return true; // Cannot be solved with the current theory, refer it as sat
    }
}

// Works only if we already had prev. asserts
z3::expr smtcheck_z3t::parse_expression_from_string(std::string str)
{
    std::string query = m_header_str + str; // Parse also with the header - KE: without it returns true
    Z3_ast parsed = Z3_parse_smtlib2_string(m_query_context,query.c_str(),0,0,0,0,0,0); 
    z3::expr e(m_query_context, parsed);
    
    return e; // Return the expression
}

z3::expr smtcheck_z3t::parse_formula_from_string(std::string str) 
{
    Z3_ast parsed = Z3_parse_smtlib2_string(m_query_context,str.c_str(),0,0,0,0,0,0); 
    z3::expr e(m_query_context, parsed);
    m_solver->add(e); // Test if valid

    Z3_error_code error = m_query_context.check_error();
    assert (error == Z3_OK && ">> ERROR:  Z3 query from string is invalid");
    
    return e;    
}

bool smtcheck_z3t::read_formula_from_file(std::string fileName)
{
    Z3_ast parsed = Z3_parse_smtlib2_file(m_query_context,fileName.c_str(),0,0,0,0,0,0); 
    z3::expr e(m_query_context, parsed);
    m_solver->add(e);

    Z3_error_code error = m_query_context.check_error();
    if (error != Z3_OK)
    {
        std::cout << ">> ERROR:  Z3 query from file " << fileName << " is invalid." << std::endl;
        return false;
    }
    
    return true;
}

z3::expr smtcheck_z3t::constant_bool(bool val)
{
    return m_query_context.bool_val(val);
}

z3::expr smtcheck_z3t::constant_to_ptref(const exprt &expr)
{
    if (expr.is_boolean()) {
        return constant_bool(expr.is_true());
    } else if (expr.type().id() == ID_c_bool) { // KE: New Cprover code - patching
        std::string num(expr.get_string(ID_value));
        assert(num.size() == 8); // if not 8, but longer, please add the case
        return constant_bool(num.compare("00000000") != 0);
    } else {
        return numeric_constant(expr);
    }    
}

FlaRef smtcheck_z3t::land(FlaRef l1, FlaRef l2){
    if (flaref_to_ptref(l1).to_string() == "true")
        return l2;
    if (flaref_to_ptref(l2).to_string() == "true")
        return l1;  
    
    // General case
    z3::expr pl1 = flaref_to_ptref(l1);
    z3::expr pl2 = flaref_to_ptref(l2);
    z3::expr ans = (pl1 && pl2);
    return push_variable(ans); // Keeps the new PTRef + create for it a new index/literal
}

FlaRef smtcheck_z3t::lor(FlaRef l1, FlaRef l2){
    if (flaref_to_ptref(l1).to_string() == "false")
        return l2;
    if (flaref_to_ptref(l2).to_string() == "false")
        return l1; 
    
    z3::expr pl1 = flaref_to_ptref(l1);
    z3::expr pl2 = flaref_to_ptref(l2);
    z3::expr ans = (pl1 || pl2);
    return push_variable(ans); // Keeps the new PTRef + create for it a new index/literal
}

FlaRef smtcheck_z3t::lor(const std::vector<FlaRef> & flas){
    assert(flas.size() > 0); // need to have something
    
    z3::expr pl = flaref_to_ptref(*flas.begin());
    for(auto it = flas.begin()+1; it != flas.end(); ++it)
    {
        pl = (pl || flaref_to_ptref(*it));
    }
    return push_variable(pl); // Keeps the new PTRef + create for it a new index/literal
}

void smtcheck_z3t::set_equal(FlaRef l1, FlaRef l2){
    z3::expr pl1 = flaref_to_ptref(l1);
    z3::expr pl2 = flaref_to_ptref(l2);
    z3::expr ans = (pl1 == pl2);
    push_variable(ans); // Keeps the new PTRef + create for it a new index/literal
    m_current_partition->push_back(ans);
}

void smtcheck_z3t::set_to_true(const z3::expr &expr){
    if (expr.is_bool())
        m_current_partition->push_back(expr);
    else {
        // If a symbol that isn't a boolena
        z3::expr truep = m_query_context.bool_val(true);
        z3::expr tlp = (expr == truep);
        m_current_partition->push_back(tlp); 
    }
}

/*******************************************************************\

Function: smtcheck_z3t::lunsupported2var --> unsupported_to_var

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
z3::expr smtcheck_z3t::unsupported_to_var(const exprt &expr) 
{    
    // Tries to map unsupported to another unsupported
    if(m_expression_to_smt_map.find(expr) != m_expression_to_smt_map.end())
        return *(m_expression_to_smt_map.find(expr))->second;

    // Create a new unsupported var
    const std::string str = m_unsupported_info.create_new_unsupported_var(expr.type().id().c_str(), false, true);
    z3::expr var = evar(expr, str);
    
    // Save to Global list
    m_unsupported_info.store_new_unsupported_var(expr,std::string(str));  

    // Return the saved flaref
    return var;
}

/*******************************************************************\

Function: smtcheck_z3t::extract_expr_str_name

  Inputs: expression that is a var

 Outputs: a string of the name

 Purpose: assure we are extracting the name correctly and in one place.
 * 
 * FIXME: more to utils

\*******************************************************************/
std::string smtcheck_z3t::extract_expr_str_name(const exprt &expr)
{
    std::string str = normalize_name(expr);
    
    //////////////////// TEST TO ASSURE THE NAME IS VALID! /////////////////////
    assert(!is_cprover_rounding_mode_var(str) && !is_cprover_builtins_var(str));    
    // MB: the IO_CONST expressions does not follow normal versioning, but why NIL is here?
    bool is_nil_or_symex = (str.compare(CProverStringConstants::NIL) == 0) || (str.find(CProverStringConstants::IO_CONST) != std::string::npos);
    assert("Error: using non-SSA symbol in the SMT encoding"
         && (is_L2_SSA_symbol(expr) || is_nil_or_symex)); // KE: can be new type that we don't take care of yet
    // If appears - please fix the code in smt_partition_target_euqationt
    // DO NOT COMMNET OUT!!! 
    ////////////////////////////////////////////////////////////////////////////
    
    return str;
}

/*******************************************************************\

Function: smtcheck_z3t::lvar

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
z3::expr smtcheck_z3t::symbol_to_ptref(const exprt &expr)
{
    // Test it is a VAR
    std::string str = extract_expr_str_name(expr); // NOTE: any changes to name - please added it to general method!
    assert(!str.empty());
    assert(expr.is_not_nil()); // MB: this assert should be stronger then the string one, the string one can probably go away
    assert(!(str.compare(CProverStringConstants::NIL) == 0 || str.compare(CProverStringConstants::QUOTE_NIL) == 0));
          
    // Else if it is really a var, continue and declare it!
    bool is_defined = (expr.type().id()!=ID_code) && 
                        (is_number(expr.type()) || (expr.is_boolean()) || (expr.type().id() == ID_c_bool));
    if (!is_defined) 
        return unsupported_to_var(expr); // push_variable is done here already 
    
    // Create the variable
    z3::expr symbol_ptref = evar(expr, str);
    
    // Add the data type constraints in LA
    add_symbol_constraints(expr, symbol_ptref);
    
    // Add to the list, and return flaref
    return symbol_ptref; // Keeps the new PTRef + create for it a new index/flaref
}

void smtcheck_z3t::store_to_cache(const exprt & expr, z3::expr l) {
    assert(m_expression_to_smt_map.find(expr) == m_expression_to_smt_map.end());
    m_expression_to_smt_map[expr] = new z3::expr{l};

    // Is needed for debug dumps and also for reading summaries!!
    const irep_idt &_id=expr.id(); 
    bool is_typecast = ((_id == ID_typecast || _id == ID_floatbv_typecast) && expr.has_operands());
    if(_id==ID_symbol || _id==ID_nondet_symbol 
            || (l.to_string()[0] == '|' && (!is_typecast) &&
                l.to_string().find(HifrogStringUnsupportOpConstants::UNSUPPORTED_VAR_NAME) != std::string::npos))
    {
        std::string name = l.to_string();
        m_header_str += "(declare-fun " + name 
                + " () " + to_string_smtlib_datatype(expr.type()) + ")\n";
    }
    // KE: Do not comment else summaries reading won't work
}

// A wrapper - due to z3::expr mechanism
z3::expr smtcheck_z3t::expression_to_ptref(const exprt &expr) { 
    if(m_expression_to_smt_map.find(expr) != m_expression_to_smt_map.end())
        return *(m_expression_to_smt_map.find(expr))->second;
#ifdef SMT_DEBUG
    cout << "\n\n; ON PARTITION " << m_partition_count << " CONVERTING with " << expr.has_operands() << " operands "<< /*expr.pretty() << */ endl;
#endif
    
    z3::expr l = convert(expr);
    store_to_cache(expr, l);
    
#ifdef SMT_DEBUG
    cout << "; For " << expr.id() << " Created Z3 formula " <<  l << endl;
#endif
    
    return l;
}
// Was convert, is now expression_to_ptref in opensmt interface
// Fits to all theories with numbers. EUF overrides it
z3::expr smtcheck_z3t::convert(const exprt &expr)
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

        return type_cast(expr);
 
    } else if (_id == ID_typecast || _id == ID_floatbv_typecast) {

        return unsupported_to_var(expr);
        // TODO: write a better suport to this case

    } else if (_id == ID_abs) {
        
        return abs_to_ptref(expr);
                
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
            return !(args[0] == args[1]);
            
        } else if(_id == ID_equal) {
            assert(args.size() == 2);
            return (args[0] == args[1]);
            
        } else if ((_id==ID_if) && (args.size()==2)) {
            return (!args[0]) || args[1];
            
        } else if ((_id==ID_if) && (args.size()==3)) {
            return z3::ite(args[0], args[1], args[2]);
            
        } else if (_id==ID_if) {
            assert(0);
            
        } else if(_id == ID_ifthenelse) {
            assert(args.size() == 3); // KE: check the case if so and add the needed code!
            return z3::ite(args[0], args[1], args[2]);  
            
        } else if(_id == ID_not) {
            assert(args.size() == 1); 
            return !args[0];
            
        } else if(_id == ID_unary_minus) {
            assert(args.size() == 1);
            return -args[0];
            
        } else if(_id == ID_unary_plus) {
            assert(args.size() == 1);
            return args[0];
            
        } else if(_id == ID_ieee_float_notequal) {
            assert(args.size() == 2);
            return !(args[0] == args[1]);

        } else if(_id == ID_ieee_float_equal) {
            assert(args.size() == 2);
            return (args[0] == args[1]); 

        } else if(_id == ID_assign) {
            assert(args.size() == 2);
            return (args[0] == args[1]); 
   
        } else if(_id == ID_implies) {
            assert(args.size() == 2);
            return (!args[0]) || args[1];

        } else if(_id == ID_ge) {
            assert(args.size() == 2);
            return args[0] >= args[1];

        } else if(_id == ID_le) {
            assert(args.size() == 2);
            return args[0] <= args[1];
  
        } else if(_id == ID_gt) {
            assert(args.size() == 2);
            return (args[0] > args[1]);
     
        } else if(_id == ID_lt) {
            assert(args.size() == 2);
            return (args[0] < args[1]);
     
        } else if(_id == ID_floatbv_minus) {
            assert(args.size() == 2);
            return args[0] - args[1];
      
        } else if(_id == ID_minus) {
            assert(args.size() == 2);
            return args[0] - args[1];  
   
        } else if(_id == ID_div) { 
            assert(args.size() == 2);            
            if (!is_linear_expression(expr))
                return unsupported_to_var(expr);
            else 
                return args[0] / args[1]; 
            
        } else if(_id == ID_floatbv_div) {
            assert(args.size() == 2);           
            if (!is_linear_expression(expr))
                return unsupported_to_var(expr);
            else
                return args[0] / args[1];   
       
        } else if(_id == ID_floatbv_plus && args.size() == 1) {   
            return args[0];   

        } else if(_id == ID_floatbv_plus && args.size() == 2) {
            return args[0] + args[1];   
      
        } else if(_id == ID_floatbv_plus) {
            assert(args.size() > 2);
            z3::expr ptl = args[0] + args[1];
            for (unsigned i = 2; i < args.size(); i++) {
               ptl = (ptl + args[i]);
            }
            return ptl;
            
        } else if(_id == ID_plus && args.size() == 1) {
            return args[0];   
         
        } else if(_id == ID_plus && args.size() == 2) {
            return args[0] + args[1];   
   
        } else if(_id == ID_plus) {              
            assert(args.size() > 2);
            z3::expr ptl = args[0] + args[1];
            for (unsigned i = 2; i < args.size(); i++) {
               ptl = (ptl + args[i]);
            }
            return ptl; // Keeps the new PTRef + create for it a new index/flaref

        } else if(_id == ID_floatbv_mult && args.size() == 1) {
            return args[0];   
      
        } else if(_id == ID_floatbv_mult && args.size() == 2) {                        
            if (!is_linear_expression(expr))
                return unsupported_to_var(expr);
            else 
                return (args[0] * args[1]);
            
        } else if(_id == ID_floatbv_mult) {
            return unsupported_to_var(expr);

        } else if(_id == ID_mult && args.size() == 1) {
            return args[0];   
         
        } else if(_id == ID_mult && args.size() == 2) {
                        
            if (!is_linear_expression(expr))
                return unsupported_to_var(expr);
            else 
                return (args[0] * args[1]);
             
        } else if(_id == ID_mult) {
            return unsupported_to_var(expr);
        
        } else if(_id == ID_and && args.size() == 1) {
            return args[0];   
    
        } else if(_id == ID_and && args.size() == 2) {
            return (args[0] && args[1]);
 
        } else if(_id == ID_and) {
            assert(args.size() > 1);
            z3::expr ptl = args[0] && args[1];
            for (unsigned i = 2; i < args.size(); i++) {
               ptl = (ptl && args[i]);
            }
            return ptl; // Keeps the new PTRef + create for it a new index/flaref
     
        } else if(_id == ID_or && args.size() == 1) {
            return args[0];   
     
        } else if(_id == ID_or && args.size() == 2) {
            return (args[0] || args[1]);
  
        } else if(_id == ID_or) {
            assert(args.size() > 2);
            z3::expr ptl = args[0] || args[1];
            for (unsigned i = 2; i < args.size(); i++) {
               ptl = (ptl || args[i]);
            }
            return ptl; // Keeps the new PTRef + create for it a new index/flaref
            
        } else if(_id == ID_xor && args.size() == 1) {
            return args[0];   
     
        } else if(_id == ID_xor && args.size() == 2) {
            return (args[0] || args[1]) && ((!args[0]) || (!args[1]));
        
        } else if(_id == ID_xor) {
            assert(args.size() > 2);
            z3::expr ptl = (args[0] || args[1]) && ((!args[0]) || (!args[1]));
            for (unsigned i = 2; i < args.size(); i++) {
               ptl = (ptl || args[i]) && ((!ptl) || (!args[i]));
            }
            return ptl; // Keeps the new PTRef + create for it a new index/flaref
                
        } else if((_id == ID_member) ||
                  (_id == ID_C_member_name) ||
                  (_id == ID_with) ||
                  (_id == ID_member_name)) { 
            
            return unsupported_to_var(expr);
            
        } else if ((_id == ID_pointer_object) ||
                  (_id==ID_index) || 
                  (_id==ID_array) || 
                  (_id==ID_struct) ||
                  (_id==ID_union) ||
                  (_id==ID_range) ||
                  (_id==ID_pointer)) {

            return unsupported_to_var(expr);
            
        } else { // Unsupported!  
            // If shall store the equation, add UF functions to the encoding
            z3::expr l = unsupported_to_var(expr);
            if (this->m_unsupported_info.is_store_unsupported_info()) {
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
            }
            
            return l;
        }
    }
}

/*******************************************************************\

Function: smtcheck_z3t::get_function_args

  Inputs:

 Outputs:

 Purpose: Convert all argument of expression and return a list

\*******************************************************************/
bool smtcheck_z3t::get_function_args(const exprt &expr, std::vector<z3::expr>& args)
{
    // True: at least one arg is unsupported
    bool res = false;
    
    // The we create the new call
    for(auto const & operand : expr.operands())
    {	
        if (is_cprover_rounding_mode_var(operand)) 
        {
            if (expr.id() == ID_mult) continue;
            if (expr.id() == ID_div) continue;
            if (expr.id() == ID_floatbv_mult) continue;
            if (expr.id() == ID_floatbv_div) continue;
        }
        // Skip - we don't need the rounding variable for non-bv logics + assure it is always rounding thing
        // if crush right after this call, add the skip case to the list above

        // Convert
        z3::expr cp = expression_to_ptref(operand);
        args.push_back(cp); // Add to call
        
        // Check if unsupported by convert
        if (cp.to_string().find(HifrogStringUnsupportOpConstants::UNSUPPORTED_VAR_NAME) != std::string::npos)
            res = true;
    }
    
    return res;
}

/*******************************************************************\

Function: smtcheck_z3t::to_string_smtlib_datatype
 * getStringSMTlibDatatype -> to_string_smtlib_datatype

  Inputs:

 Outputs:

 Purpose:

 * For exprt, use typet type = expr.type(); // Get the current type
\*******************************************************************/
std::string smtcheck_z3t::to_string_smtlib_datatype(const typet& type)
{
    return get_smtlib_datatype(type).to_string();
}


/*******************************************************************\

Function: smtcheck_z3t::get_smtlib_datatype
 * getSMTlibDatatype --> get_smtlib_datatype

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
z3::sort smtcheck_z3t::get_smtlib_datatype(const typet& type)
{
    if ((type.id()==ID_bool) || (type.id() == ID_c_bool))
        return m_query_context.bool_sort();
    if (is_number(type))
        return get_numeric_sort();
    
    // Assume arrays/pointer assume an numeric presentation
    //std::cout << "Warning: Unknown datatype encountered!\n";
    return get_numeric_sort();
}

/*******************************************************************\

Function: smtcheck_z3t::create_unsupported_uf_call

  Inputs:

 Outputs:

 Purpose:

 *  If not exist yet, creates a new declartion in OpenSMT with 
 *  function name+size of args+type. 
 *  Add a new ptref of the use for this expression
\*******************************************************************/
z3::expr smtcheck_z3t::create_unsupported_uf_call(const exprt &expr)
{  
    // Interface function - declare_unsupported_function shall work for any solver 
    // KE: do not refactor and sent args to the method, shall work for any solver!
    std::string decl_str = m_unsupported_info.declare_unsupported_function(expr);
    if (decl_str.size() == 0)
        return m_query_context.bool_val(true);
    
    z3::func_decl decl = m_unsupported_info.get_declaration(decl_str);
    
    std::vector<z3::expr> args;
    get_function_args(expr, args);
        
    if (args.size() == 1) {
        z3::expr ret = decl(args[0]);
        return ret;
    } else if (args.size() == 2) {
        z3::expr ret = decl(args[0], args[1]);
        return ret;
    } else if (args.size() == 3) {
        z3::expr ret = decl(args[0], args[1], args[2]);
        return ret;
    } else if (args.size() == 4) {
        z3::expr ret = decl(args[0], args[1], args[2], args[3]);
        return ret;
    } else if (args.size() == 5) {
        z3::expr ret = decl(args[0], args[1], args[2], args[3], args[4]);
        return ret;
    } else {
        // TODO
        assert(0);
    }
}

/*******************************************************************\

Function: smtcheck_z3t::flaref_to_ptref

  Inputs:

 Outputs:

 Purpose: to support overriden operators in FlaRef class
 * FIXME: move to pattern format out of the solver interfaces classes
 
\*******************************************************************/
z3::expr smtcheck_z3t::flaref_to_ptref(FlaRef l) {
    
    if(l.is_constant()){
        return ((l.is_true()) ? m_query_context.bool_val(true) : m_query_context.bool_val(false));
    }
    assert(l.no() < m_flaref2exprs.size());
    z3::expr ptref = m_flaref2exprs[l.no()];
    return l.sign() ? !ptref : ptref;
}

void smtcheck_z3t::insert_substituted(const itpt & itp, const std::vector<symbol_exprt> & symbols) {
    assert(!itp.is_trivial());
    assert(m_solver);  
    auto const & smt_itp_z3 = static_cast<smt_itp_z3t const &> (itp);
    
    // Go over all symbols - check valid signature
    std::string args = smt_itp_z3.getArgs();    
    std::size_t start_pos = args.find("|");
    for(std::size_t i = 0; i < symbols.size(); ++i){
        std::string symbol_name { get_symbol_name(symbols[i]).c_str() }; // L0
        std::size_t end_pos = args.find("|", start_pos+1);
        std::string argument_name = args.substr(start_pos+1, end_pos-start_pos-1);        
        if(symbol_name != argument_name){
            std::stringstream ss;
                ss << "Argument name read from summary do not match expected symbol name!\n"
                    << "Expected symbol name: " << symbol_name << "\nName read from summary: " << argument_name;

            throw std::logic_error(ss.str());
        }
        
        start_pos = args.find("|", end_pos+1);
    }
    
    // substitute L0 in L2
    std::string new_itp = smt_itp_z3.getInterpolant(); // get the body
    // Go over all symbols and substitute
    for(std::size_t i = 0; i < symbols.size(); ++i){
        std::string symbol_name { quote_if_necessary(get_symbol_name(symbols[i]).c_str()) }; // L0
        z3::expr ptref = expression_to_ptref(symbols[i]); // L2 to expression      
        new_itp = replace_all( new_itp, symbol_name, ptref.to_string()); // replace all symbol_name to ptref in new_itp
    }
    
    // Set to true + assert + push to the solver!
    new_itp = "(assert " + new_itp + ")";
    z3::expr e = this->parse_expression_from_string(new_itp);
    set_to_true(e);
}

/*******************************************************************\

Function: smtcheck_z3t::push_assumes2type

  Inputs:

 Outputs:

 Purpose: option 1,2

\*******************************************************************/
void smtcheck_z3t::push_assumes2type(
        const z3::expr var,
        std::string lower_b,
        std::string upper_b)
{
    if (get_type_constraints_level() < 1 ) return;
    z3::expr ptr = create_constraints2type(var, lower_b, upper_b);;
    set_to_true(ptr);
}

/*******************************************************************\

Function: smtcheck_z3t::push_asserts2type

  Inputs:

 Outputs:

 Purpose: option 2

\*******************************************************************/
void smtcheck_z3t::push_asserts2type(
        const z3::expr var,
        std::string lower_b,
        std::string upper_b)
{
    if (get_type_constraints_level() < 2) return;

    // Else add the checks
    add_to_asset_expr(create_constraints2type(var, lower_b, upper_b));
}

/*******************************************************************\

Function: smtcheck_z3t::push_constraints2type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
bool smtcheck_z3t::push_constraints2type(
        const z3::expr var,
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

Function: smtcheck_z3t::add_constraints2type

  Inputs:

 Outputs:

 Purpose: If the expression is a number adds constraints
 * TODO: move out of the class

\*******************************************************************/
void smtcheck_z3t::add_constraints2type(const exprt & expr, const z3::expr var)
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
    int size = var_type.get_size_t("width");
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
            << var_type.get_size_t("width") << "bits"
            << endl;
#endif
}