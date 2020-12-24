/*******************************************************************
 * File:   hifrog_symex_target_equation_no_partition.h
 * Author: karinek
 * Created on 21 April 2017
 *******************************************************************/
#ifndef HIFROG_SYMEX_TARGET_EQUATIONT_NO_PARTITION_H
#define HIFROG_SYMEX_TARGET_EQUATIONT_NO_PARTITION_H

#include <goto-symex/symex_target_equation.h>
#include <goto-symex/ssa_step.h>
class convertort;

class hifrog_symex_target_equationt:public symex_target_equationt
{
public:
    hifrog_symex_target_equationt(const namespacet &_ns) :
        symex_target_equationt(),
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
        
    virtual ~hifrog_symex_target_equationt()
    {
#         ifdef DISABLE_OPTIMIZATIONS        
	  partition_smt_decl->clear();
	  delete partition_smt_decl;        
	  first_call_expr = 0; // Not here to do the delete
#         endif
    }

    // Convert all the SSA steps into the corresponding formulas in
    // the corresponding partitions
    void convert(convertort &convertor);

    std::vector<exprt>& get_exprs_to_refine () { return exprs; }; 
    
#ifdef DISABLE_OPTIMIZATIONS  
    void set_dump_SSA_tree(bool f) { dump_SSA_tree = f;}
    void set_dump_SSA_tree_name(const std::string& n)
    {
      ssa_tree_file_name = "__SSA_" + n;
    }
#endif  
  
protected:
    // Convert a specific partition guards of SSA steps
    void convert_guards(convertort &convertor);
    // Convert a specific partition assignments of SSA steps
    void convert_assignments(convertort &convertor);
    // Convert a specific partition assumptions of SSA steps
    void convert_assumptions(convertort &convertor);
    // Convert a specific partition assertions of SSA steps
    void convert_assertions(convertort &convertor);
    // Convert a specific partition io of SSA steps
    void convert_io(convertort &convertor);
    // Convert a summary partition (i.e., assert its summary)
    void convert_summary(convertort &convertor);
    // Convert Gotos of SSA steps
    void convert_goto_instructions(convertort &convertor);
    // Convert constraints
    void convert_constraints(convertort &convertor) const;

    std::vector<exprt> exprs; // Expr to refine method
public:
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
       
    bool isPropBuiltinEq(const exprt &expr); // Detect the case of added round var for rounding model- not needed in LRA!
    
    unsigned io_count_global; // KE: for Inputs in SSA expression - new CProver version can have more than one input entry
};

#endif /* HIFROG_SYMEX_TARGET_EQUATIONT_NO_PARTITION_H */
