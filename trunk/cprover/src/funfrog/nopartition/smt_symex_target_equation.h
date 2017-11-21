/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   smt_symex_target_equation.h
 * Author: karinek
 *
 * Created on 21 April 2017, 11:33
 */

#ifndef SMT_SYMEX_TARGET_EQUATIONT_H
#define SMT_SYMEX_TARGET_EQUATIONT_H

#include <goto-symex/symex_target_equation.h>

class smtcheck_opensmt2t;

// No need to take anything from partition_target_equation, only from the
// sub smt class of it
class smt_symex_target_equationt:public symex_target_equationt 
{
public:
    smt_symex_target_equationt(const namespacet &_ns,
            std::vector<unsigned>& _clauses) :
        symex_target_equationt(_ns),
        clauses(_clauses),
#       ifdef DISABLE_OPTIMIZATIONS
        dump_SSA_tree(false),
        ssa_tree_file_name("__ssa_tree_default"),
        out_local_terms(0),
        out_terms(out_local_terms),
        out_local_basic(0),
        out_basic(out_local_basic),
        out_local_partition(0),
        out_partition(out_local_partition),
        terms_counter(0),
        is_first_call(true),
        first_call_expr(0),
        #endif                                  
        io_count_global(0)
    {
#ifdef DISABLE_OPTIMIZATIONS  
	  partition_smt_decl = new std::map <std::string,exprt>();
	  out_terms.rdbuf(&terms_buf);
	  out_basic.rdbuf(&basic_buf);
	  out_partition.rdbuf(&partition_buf);
#endif            
    }
        
    virtual ~smt_symex_target_equationt() 
    {
#         ifdef DISABLE_OPTIMIZATIONS        
	  partition_smt_decl->clear();
	  delete partition_smt_decl;        
	  first_call_expr = 0; // Not here to do the delete
#         endif
    }

    // Convert all the SSA steps into the corresponding formulas in
    // the corresponding partitions
    void convert(smtcheck_opensmt2t &decider);
  
    //void fill_function_templates(smtcheck_opensmt2t &decider, vector<summaryt*> &templates)
    //{ /* TODO ! */ }
  
    // Extract interpolants corresponding to the created partitions
    //void extract_interpolants(
    //    interpolating_solvert& interpolator, const smtcheck_opensmt2t& decider)
    //{ /* TODO ! */ }

    std::vector<exprt>& get_exprs_to_refine () { return exprs; }; 
    
#ifdef DISABLE_OPTIMIZATIONS  
    void set_dump_SSA_tree(bool f) { dump_SSA_tree = f;}
    void set_dump_SSA_tree_name(const std::string& n)
    {
      ssa_tree_file_name = "__SSAt_" + n;
    }
#endif  
  
protected:
    // Convert a specific partition guards of SSA steps
    void convert_guards(smtcheck_opensmt2t &decider);
    // Convert a specific partition assignments of SSA steps
    void convert_assignments(smtcheck_opensmt2t &decider);
    // Convert a specific partition assumptions of SSA steps
    void convert_assumptions(smtcheck_opensmt2t &decider);
    // Convert a specific partition assertions of SSA steps
    void convert_assertions(smtcheck_opensmt2t &decider);
    // Convert a specific partition io of SSA steps
    void convert_io(smtcheck_opensmt2t &decider);
    // Convert a summary partition (i.e., assert its summary)
    void convert_summary(smtcheck_opensmt2t &decider);
    // Convert Gotos of SSA steps
    void convert_goto_instructions(smtcheck_opensmt2t &decider);
    // Convert constraints
    void convert_constraints(smtcheck_opensmt2t &decider) const;  
  
  
    virtual bool is_smt_encoding() {return true;} // KE: Temp. Just to force virtual for compilation

    std::vector<exprt> exprs; // Expr to refine method
private:
    // MB: FIXME: this field is not used! Why it is here?
    // KE: a good question, maybe Grigory will have an answer. It is also in the partition version
    std::vector<unsigned>& clauses;
    
    bool isRoundModelEq(const exprt &expr); // Detect the case of added round var for rounding model- not needed in LRA!

#ifdef DISABLE_OPTIMIZATIONS 
    bool dump_SSA_tree;
    std::string ssa_tree_file_name;
    
    // For SMT-Lib Translation - Move it later to a new class
    std::map <std::string,exprt>* partition_smt_decl;
    std::ostream out_local_terms; //for prints SSA - remove later
    std::ostream& out_terms; // for prints SSA - remove later
    std::stringbuf terms_buf; // for prints SSA - remove later

    std::ostream out_local_basic; //for prints SSA - remove later
    std::ostream& out_basic; // for prints SSA - remove later
    std::stringbuf basic_buf; // for prints SSA - remove later

    std::ostream out_local_partition; //for prints SSA - remove later
    std::ostream& out_partition; // for prints SSA - remove later
    std::stringbuf partition_buf; // for prints SSA - remove later

    int terms_counter; // for prints SSA - remove later
    bool is_first_call; // for prints SSA - remove later
    const exprt* first_call_expr; // for prints SSA - remove later

    // Print decl (later change to create) - Copied from the partition classes
    std::ostream& print_decl_smt(std::ostream& out);
    void print_all_partition(std::ostream& out);
    void print_partition();  
    void saveFirstCallExpr(const exprt& expr);
    bool isFirstCallExpr(const exprt& expr);
#endif
       
    unsigned io_count_global; // KE: for Inputs in SSA expression - new CProver version can have more than one input entry
};

#endif /* SMT_SYMEX_TARGET_EQUATIONT_H */
