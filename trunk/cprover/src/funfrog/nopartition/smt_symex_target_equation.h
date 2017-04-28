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
#include <symbol.h>
#include <type.h>

#include "../solvers/itp.h"
#include "../solvers/smtcheck_opensmt2.h"

// No need to take anything from partition_target_equation, only from the
// sub smt class of it
class smt_symex_target_equationt:public symex_target_equationt 
{
public:
    smt_symex_target_equationt(const namespacet &_ns,
            std::vector<unsigned>& _clauses) :
        symex_target_equationt(_ns),
        clauses(_clauses),
        io_count_global(0)
    {}
        
    virtual ~smt_symex_target_equationt() {}

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

};

#endif /* SMT_SYMEX_TARGET_EQUATIONT_H */
