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

#include "../expr_pretty_print.h"
#include <goto-symex/symex_target_equation.h>
#include <symbol.h>
#include <type.h>

#include "../solvers/itp.h"
#include "../solvers/smtcheck_opensmt2.h"

//#define DEBUG_SSA_PRINT // Print the SSA encoding + recompile expr_pretty_print class


// No need to take anything from partition_target_equation, only from the
// sub smt class of it
class smt_symex_target_equationt:public symex_target_equationt 
{
public:
    smt_symex_target_equationt(const namespacet &_ns,
            std::vector<unsigned>& _clauses) :
        symex_target_equationt(_ns),
        clauses(_clauses),
#       ifdef DEBUG_SSA_PRINT
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
#ifdef DEBUG_SSA_PRINT  
	  partition_smt_decl = new std::map <std::string,exprt>();
	  out_terms.rdbuf(&terms_buf);
	  out_basic.rdbuf(&basic_buf);
	  out_partition.rdbuf(&partition_buf);
#endif            
    }
        
    virtual ~smt_symex_target_equationt() 
    {
#         ifdef DEBUG_SSA_PRINT        
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

  
    virtual bool is_smt_encoding() {return true;} // KE: Temp. Just to force virtual for compilation

    std::vector<exprt> exprs; // Expr to refine method
private:
    std::vector<unsigned>& clauses;

    unsigned io_count_global; // KE: for Inputs in SSA expression - new CProver version can have more than one input entry
    
    bool isRoundModelEq(const exprt &expr); // Detect the case of added round var for rounding model- not needed in LRA!

#ifdef DEBUG_SSA_PRINT  
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

    // Print decl (later change to create) 
    std::ostream& print_decl_smt(std::ostream& out);
    void print_all_partition(std::ostream& out);
    void print_partition();  
    void addToDeclMap(const exprt &expr);
    void saveFirstCallExpr(const exprt& expr);
    bool isFirstCallExpr(const exprt& expr);
#endif
    
    
};

#endif /* SMT_SYMEX_TARGET_EQUATIONT_H */
