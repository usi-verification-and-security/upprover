/*******************************************************************\

Module: Wrapper for Z3

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_Z3_H
#define CPROVER_SMTCHECK_Z3_H

#include <z3++.h>
#include <z3_api.h>
using namespace z3;

#include <ostream>
#include <vector>
#include <util/expr.h>
#include <util/symbol.h>

#include "solver_options.h"
#include "../utils/expressions_utils.h"
#include "../utils/unsupported_operations_z3.h" // KE: shall move all the code of unsupported here
#include "funfrog/interface/convertor.h"
#include "funfrog/interface/ssa_solvert.h"

// For interpolation
#ifdef PRODUCE_PROOF
class smt_itp_z3t;
#endif

// Here PTRef of OpenSMT replaced with z3::expr 
// TODO:  add interpolation calls from z3
// public interpolating_solvert - experimental
class smtcheck_z3t :  public interpolating_solvert, public solvert, public convertort, public ssa_solvert
{
public:
    // Defualt C'tor
    smtcheck_z3t(const solver_optionst solver_options, std::string _logic);
        
    virtual ~smtcheck_z3t(); // d'tor
    
    // ********************* methods implementing ssa_solvert interface ***************************************
#ifdef PRODUCE_PROOF
    interpolating_solvert* get_interpolating_solver() override { return this; }
#endif // PRODUCE_PROOF
    solvert* get_solver() override { return this; }

    convertort* get_convertor() override { return this; }
    // *********************************************************************************************************    
    
    virtual bool solve() override; // Common to all
    
    virtual bool is_assignment_true(FlaRef a) const override; // Common to all

    virtual fle_part_idt new_partition() override; // Common to all

    void close_partition() override; // Common to all
    
    virtual FlaRef convert_bool_expr(const exprt &expr) override{
        assert(is_boolean(expr));
        return push_variable(expression_to_ptref(expr));
    }
    
    virtual FlaRef land(FlaRef l1, FlaRef l2) override; // Common to all

    virtual FlaRef lor(FlaRef l1, FlaRef l2) override; // Common to all
 
    virtual FlaRef lor(const std::vector<FlaRef> & flas) override; // Common to all

    virtual void set_equal(FlaRef l1, FlaRef l2) override; // Common to all
    
    template<typename Container>
    void assert_literals(const Container& c){
        for(auto lit : c){
            assert_literal(lit);
        }
    }
    
    void assert_literal(const FlaRef lit) override {
        m_current_partition->push_back(flaref_to_ptref(lit));
    }

    void set_to_true(const exprt &expr) override {
        auto l = convert_bool_expr(expr);
        assert_literal(l);
    }

    void set_to_false(const exprt &expr) override{
        auto l = convert_bool_expr(expr);
        assert_literal(!l); // assert the negation
    }
    
    FlaRef limplies(FlaRef a, FlaRef b) override
    {
        FlaRef a_not = push_variable(flaref_to_ptref(!a));
        return lor(a_not, b);
    }
         
    virtual FlaRef get_and_clear_var_constraints() override 
    { return const_formula(true); } // Replace lassert in non-incremental solving mode
        
    virtual void insert_substituted(const itpt & itp, const std::vector<symbol_exprt> & symbols) override;// Common to all    
    
#ifdef PRODUCE_PROOF  
    // Extracts the symmetric interpolant of the specified set of
    // partitions. This method can be called only after solving the
    // the formula with an UNSAT result
    virtual void get_interpolant(const interpolation_taskt& partition_ids,
      interpolantst& interpolants) const override
    { assert(0); } // TODO: test interpolation for z3

    // Is the solver ready for interpolation? I.e., the solver was used to decide
    // a problem and the result was UNSAT
    virtual bool can_interpolate() const override 
    { return false; } // Enable when interpolation works
    //{  return m_ready_to_interpolate; }
    
    virtual void generalize_summary(itpt * interpolant, std::vector<symbol_exprt> & common_symbols) override
    { assert(0); } // TODO: test interpolation for z3
    
    void generalize_summary(smt_itp_z3t & interpolant, std::vector<symbol_exprt> & common_symbols)
    { assert(0); } // TODO: test interpolation for z3
    
#endif    
    
    virtual void set_random_seed(unsigned int i) override; // Common to all

    virtual unsigned get_random_seed() override { return m_solver_options.m_random_seed; } // Common to all

    bool read_formula_from_file(std::string fileName);
    
    std::string to_string_smtlib_datatype(const typet& type);

    virtual bool is_overapprox_encoding() const override
    { return (m_unsupported_info.has_unsupported_vars() && !has_overappox_mapping());}
    
    bool has_overappox_mapping() const  
    { return m_unsupported_info.has_unsupported_info(); }
    
    void init_unsupported_counter() { m_unsupported_info.init_unsupported_counter(); }
    unsupported_operationst& get_unsupported_info() { return m_unsupported_info;}
        
    virtual exprt get_value(const exprt &expr) override;
    
    virtual z3::sort get_numeric_sort()=0;
    
    bool get_function_args(const exprt &expr, std::vector<z3::expr>& args);
    
    z3::sort get_smtlib_datatype(const typet& type);
    
protected:
    z3::context m_query_context;

    z3::solver* m_solver;
 
    std::string m_logic; //const char *
    
    using expr_hasht = irep_hash; // dstring or string, doesn't really matter the type name
    std::unordered_map<exprt, z3::expr*, expr_hasht> m_expression_to_smt_map; // cash
    
    //  Mapping from boolean variable indexes to their PTRefs
    std::vector<z3::expr> m_flaref2exprs;
    typedef std::vector<z3::expr>::iterator it_flarefs;
    
    // Count of the created partitions
    unsigned m_partition_count=0;

    //  List of clauses that are part of this partition (a.k.a. assert in smt2lib)
    std::vector<z3::expr>* m_current_partition;
  
    std::vector<z3::expr> m_top_level_formulas;
      
    unsigned m_no_flarefs;
    
    unsigned m_no_flarefs_last_solved;
    
    unsigned m_pushed_formulas;
    
    unsupported_operations_z3t m_unsupported_info;

    solver_optionst m_solver_options;
    
    bool m_last_partition_closed = true;

    std::string m_header_str;

#ifdef DISABLE_OPTIMIZATIONS  
    // Dump all queries?
    bool          m_dump_queries;
    bool          m_dump_pre_queries;
    std::string   m_base_dump_query_name;
    std::string   m_pre_queries_file_name;

    
    std::map <std::string,std::string> ite_map_str;
    std::set <std::string> var_set_str;
    typedef std::map<std::string,std::string>::iterator it_ite_map_str;
    typedef std::set<std::string>::iterator it_var_set_str;
#endif   
    
#ifdef PRODUCE_PROOF    
    bool m_ready_to_interpolate = false;
#endif     
    
    FlaRef new_variable();
    
    FlaRef push_variable(z3::expr ptl);
    
    virtual z3::expr evar(const exprt &expr, std::string var_name)=0;
    
    void set_to_true(const z3::expr &expr);
    
    z3::expr expression_to_ptref(const exprt &expr);
    
    virtual z3::expr convert(const exprt &expr);  // UF overrides it
    
    z3::expr unsupported_to_var(const exprt &expr); // for inner convert
    
    z3::expr symbol_to_ptref(const exprt &expr); // for inner convert
    
    z3::expr constant_to_ptref(const exprt &expr); // for inner convert
    
    virtual z3::expr numeric_constant(const exprt &expr)=0; // for inner convert
    
    virtual z3::expr type_cast(const exprt &expr)=0; // for inner convert
    
    virtual z3::expr abs_to_ptref(const exprt &expr) { assert(0); } // for inner convert
    
    virtual z3::expr constant_bool(bool val);// Common to all - interface get_const_flaref
      
    std::string extract_expr_str_name(const exprt &expr);
    
    void store_to_cache(const exprt & expr, z3::expr l);
    
    z3::expr create_unsupported_uf_call(const exprt &expr);
    
    // FIXME: shall be a tamplate method outside the solvers classes
    // Used only in check_opensmt2 sub-classes
    z3::expr flaref_to_ptref(FlaRef l);
    
    z3::expr parse_expression_from_string(std::string str);
    
    z3::expr parse_formula_from_string(std::string str);
    
    virtual void add_symbol_constraints(const exprt &expr, const z3::expr var) {} //--type constraints
    
    void add_constraints2type(const exprt & expr, const z3::expr var); // --type-constraints
    
    bool push_constraints2type(const z3::expr var, bool is_non_det, std::string lower_b, std::string upper_b); // --type-constraints
    
    void push_asserts2type(const z3::expr var, std::string lower_b, std::string upper_b); // --type-constraints
    
    void push_assumes2type(const z3::expr var, std::string lower_b, std::string upper_b); // --type-constraints
    
    virtual void add_to_asset_expr(z3::expr constraint)=0; // --type-constraints
    
    virtual z3::expr create_constraints2type(const z3::expr var, std::string lower_b, std::string upper_b)=0; // --type-constraints
    
    virtual unsigned get_type_constraints_level()=0; // --type-constraints
    
};

#endif
