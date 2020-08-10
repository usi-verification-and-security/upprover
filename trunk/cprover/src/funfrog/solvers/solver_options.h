/*******************************************************************\
 * Module:   solver_options
 * Author: karinek
 * Created on 24 August 2018
 * 
 * Please Add any new option here (not manually to the class)
\*******************************************************************/

#ifndef SOLVER_OPTIONS_H
#define SOLVER_OPTIONS_H

#include <string>

class solver_optionst {
public:
    
    // General options of Numeric solver (LRA, LIA, NRA, ...)
    void initialize_numeric_solver_options(unsigned _type_constraints)
    {m_type_constraints=_type_constraints;}
    
    // Mix-encoding options for such solvers
    void initialize_mix_encoding_solver_options(unsigned _byte_type_constraints, unsigned _bitwidth)
    {m_byte_type_constraints=_byte_type_constraints;m_bitwidth=_bitwidth;}
     
    // Debug options
#ifdef DISABLE_OPTIMIZATIONS
    void initialize_solver_debug_options(bool _dump_query, bool _dump_pre_query, std::string _dump_query_name)
    {m_dump_query=_dump_query;m_dump_pre_query=_dump_pre_query;m_dump_query_name=_dump_query_name;}
#endif // DISABLE_OPTIMIZATIONS    
    
    
// All Data members - in public
    unsigned m_verbosity = 0;
    unsigned m_random_seed = 1;
    bool m_store_unsupported_info = false;
    bool m_incremental_solver = false; // TODO: make it work for OpenSMT2

#ifdef PRODUCE_PROOF
    unsigned m_certify=0;
    bool m_do_reduce=false;
    unsigned m_reduction_loops=3;
    unsigned m_reduction_graph=2;
    
    // Prop
    int m_prop_itp_algorithm=0;
    
    // LRA
    //the default LRA interpolation algorithm
    unsigned m_lra_itp_algorithm=4;
    std::string m_lra_factor="1/2";
    
    // UF
    unsigned m_uf_itp_algorithm=0;
#endif // PRODUCE_PROOF
    
    // All Numeric
    unsigned m_type_constraints=1;
    
    // Mix-encoding with bit-vectors
    unsigned m_byte_type_constraints=0;
    unsigned m_bitwidth=8;
    
#ifdef DISABLE_OPTIMIZATIONS
    bool m_dump_query=false;
    bool m_dump_pre_query=false;
    std::string m_dump_query_name="__pre_query_default";
#endif // DISABLE_OPTIMIZATIONS
};

#endif /* SOLVER_OPTIONS_H */

