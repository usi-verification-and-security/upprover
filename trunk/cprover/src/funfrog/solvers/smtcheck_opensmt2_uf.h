/*******************************************************************\

Module: Wrapper for OpenSMT2

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_OPENSMT2_UF_H
#define CPROVER_SMTCHECK_OPENSMT2_UF_H

#include "smtcheck_opensmt2.h"

class smtcheck_opensmt2t_uf : public smtcheck_opensmt2t
{
public:
  smtcheck_opensmt2t_uf(const char* name, 
#ifdef PRODUCE_PROOF   
        unsigned int _itp_uf_algorithm,
        bool _reduction, 
        unsigned int _reduction_graph, 
        unsigned int _reduction_loops,   
#endif
#ifdef DISABLE_OPTIMIZATIONS          
        bool _dump_queries, bool _dump_pre_queries, std::string _dump_query_name,
#endif          
        bool _store_unsupported_info=false) :
    smtcheck_opensmt2t(
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
    
// Init of Interpolation
#ifdef PRODUCE_PROOF
    itp_euf_algorithm.x = _itp_uf_algorithm;
#endif    
  }

  virtual ~smtcheck_opensmt2t_uf(); // d'tor
  
  virtual exprt get_value(const exprt &expr) override;

  virtual literalt convert(const exprt &expr) override;
       
  virtual std::string getStringSMTlibDatatype(const typet& type) override;
  virtual SRef getSMTlibDatatype(const typet& type) override;
  SRef getURealSortRef() const {return sort_ureal;}
  
protected:
  
    virtual void initializeSolver(const char* name) override;
    
    virtual literalt lconst_number(const exprt &expr) override;

    virtual literalt ltype_cast(const exprt &expr) override;
  
    virtual PTRef evar(const exprt &expr, std::string var_name) override;
    
    virtual literalt lunsupported2var(const exprt &expr) override; // for isnan, mod, arrays ect. that we have no support (or no support yet) create over-approx as nondet

    virtual PTRef make_var(const std::string name) override
    { return logic->mkVar(sort_ureal, name.c_str()); }
  
    virtual bool can_have_non_linears() override { return true; }
  
     virtual bool is_non_linear_operator(PTRef tr) override;
 
private:  

  static const char *tk_sort_ureal;
  static const char *tk_mult;
  static const char *tk_div;
  static const char *tk_plus;
  static const char *tk_minus;
  static const char *tk_lt;
  static const char *tk_le;
  static const char *tk_gt;
  static const char *tk_ge;
  static const char *tk_neg;

  SRef sort_ureal; //Uninterpreted Real sort. Used to fake LRA.
  SymRef s_mult, s_div, s_plus, s_minus;
  SymRef s_lt, s_le, s_gt, s_ge;
  SymRef s_neg;

  // Only for UF
  PTRef mkURealMult(vec<PTRef>& args);
  PTRef mkURealDiv(vec<PTRef>& args);
  PTRef mkURealPlus(vec<PTRef>& args);
  PTRef mkURealMinus(vec<PTRef>& args);
  PTRef mkURealLt(vec<PTRef>& args);
  PTRef mkURealLe(vec<PTRef>& args);
  PTRef mkURealGt(vec<PTRef>& args);
  PTRef mkURealGe(vec<PTRef>& args);

};

#endif
