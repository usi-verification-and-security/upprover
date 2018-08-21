/*******************************************************************\

Module: Wrapper for OpenSMT2

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_OPENSMT2_LRA_H
#define CPROVER_SMTCHECK_OPENSMT2_LRA_H

#include "smtcheck_opensmt2_la.h"

class smtcheck_opensmt2t_lra : public smtcheck_opensmt2t_la
{
public:
  smtcheck_opensmt2t_lra(unsigned int _type_constraints_level, const char* name, 
#ifdef PRODUCE_PROOF   
        unsigned int _itp_lra_algorithm,
        const char *_itp_lra_factor, 
        bool _reduction, 
        unsigned int _reduction_graph, 
        unsigned int _reduction_loops,  
#endif
#ifdef DISABLE_OPTIMIZATIONS          
        bool _dump_queries, bool _dump_pre_queries, std::string _dump_query_name,
#endif          
        bool _store_unsupported_info=false) :
    smtcheck_opensmt2t_la(_type_constraints_level,
#ifdef PRODUCE_PROOF  
        _reduction, _reduction_graph, _reduction_loops
#else
        false, 3, 2
#endif // Is last always!
#ifdef DISABLE_OPTIMIZATIONS
        , _dump_queries, _dump_pre_queries, _dump_query_name 
#endif  
        , _store_unsupported_info)
  {
    initializeSolver(name);
    
// Init of Interpolation - TODO: move into initializeSolver
#ifdef PRODUCE_PROOF
    itp_lra_algorithm.x = _itp_lra_algorithm;
    itp_lra_factor = _itp_lra_factor; 
#endif
  }
      
  virtual ~smtcheck_opensmt2t_lra(); // d'tor
  
  virtual literalt labs(const exprt &expr) override; // from convert for ID_abs

  void check_ce(std::vector<exprt>& exprs); // checking spuriousness of the error trace (not refinement here)
  
  virtual std::string getStringSMTlibDatatype(const typet& type) override;
  virtual SRef getSMTlibDatatype(const typet& type) override;

protected:
    
  virtual void initializeSolver(const char*) override;
  
  virtual literalt ltype_cast(const exprt &expr) override;

};

#endif
