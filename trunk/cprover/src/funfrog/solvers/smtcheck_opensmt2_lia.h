/*******************************************************************\

Module: Wrapper for OpenSMT2

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_OPENSMT2_LIA_H
#define CPROVER_SMTCHECK_OPENSMT2_LIA_H

#include "smtcheck_opensmt2_la.h"

class smtcheck_opensmt2t_lia : public smtcheck_opensmt2t_la
{
public:
  smtcheck_opensmt2t_lia(unsigned int _type_constraints_level, const char* name, 
#ifdef PRODUCE_PROOF   
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
  }
      
  virtual ~smtcheck_opensmt2t_lia(); // d'tor

  virtual literalt labs(const exprt &expr) override; // from convert for ID_abs

  virtual std::string getStringSMTlibDatatype(const typet& type) override;
  virtual SRef getSMTlibDatatype(const typet& type) override;
  
// KE: FIXME remove this code till the end of the endif after OpenSMT has support for LIA interpolation
#ifdef PRODUCE_PROOF
  virtual void get_interpolant(const interpolation_taskt& partition_ids,
      interpolantst& interpolants) override {assert(0);}

  virtual bool can_interpolate() const override {assert(0);}

  // Extract interpolant form OpenSMT files/data
  virtual void extract_itp(PTRef ptref, smt_itpt& target_itp) const {assert(0);}

  void generalize_summary(smt_itpt& interpolant, std::vector<symbol_exprt>& common_symbols,
                          const std::string& fun_name, bool substitute) override {assert(0);}
#endif  

protected:

  virtual void initializeSolver(const char*) override;

  virtual literalt ltype_cast(const exprt &expr) override;
  
};

#endif
