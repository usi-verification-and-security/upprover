/*******************************************************************\

Module: Wrapper for OpenSMT2

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_OPENSMT2_LA_H
#define CPROVER_SMTCHECK_OPENSMT2_LA_H

#include "smtcheck_opensmt2.h"

class smtcheck_opensmt2t_la : public smtcheck_opensmt2t
{
public:
  smtcheck_opensmt2t_la(unsigned int _type_constraints_level, 
#ifdef PRODUCE_PROOF   
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
        , _store_unsupported_info),
    type_constraints_level(_type_constraints_level)
  { } // Virtual class
      
  virtual ~smtcheck_opensmt2t_la(); // d'tor

  virtual exprt get_value(const exprt &expr) override;

  virtual literalt convert(const exprt &expr) override;

  virtual literalt const_from_str(const char* num); // needed for error_trace

  virtual literalt lassert(const exprt &expr) override;
  
  virtual literalt labs(const exprt &expr)=0;
  
protected:
  void initializeSolver(const char*) override;

  PTRef mult_numbers(const exprt &expr, vec<PTRef> &args);

  PTRef div_numbers(const exprt &expr, vec<PTRef> &args);

  // for isnan, mod, arrays etc. that we have no support (or no support yet) create over-approx as nondet
  virtual literalt lunsupported2var(const exprt &expr) override;

  PTRef runsupported2var(const exprt &expr);

  bool isLinearOp(const exprt &expr, vec<PTRef> &args); // Check if we don't do sth. like nondet*nondet, but only const*nondet (e.g.)

  virtual bool can_have_non_linears() override{ return false; }
  
  virtual bool is_non_linear_operator(PTRef tr) override;

  /* Set of functions that add constraints to take care of overflow and underflow */
  void add_constraints2type(const exprt &expr, PTRef& var); // add assume/assert on the data type

  bool push_constraints2type(
  		PTRef &var,
		bool is_non_det,
  		std::string lower_b,
  		std::string upper_b); // Push the constraints of a data type

  void push_assumes2type(
  		PTRef &var,
  		std::string lower_b,
  		std::string upper_b); // Push assume to the higher level

  void push_asserts2type(
  		PTRef &var,
  		std::string lower_b,
  		std::string upper_b); // Push assert to the current partition

  literalt create_constraints2type(
  		PTRef &var,
  		std::string lower_b,
  		std::string upper_b); // create a formula with the constraints
  
  virtual PTRef make_var(const std::string name) override
  { return lalogic->mkNumVar(name.c_str()); }
  
  virtual literalt lconst_number(const exprt &expr) override;

  literalt ltype_cast(const exprt &expr) override;
  
  virtual PTRef evar(const exprt &expr, std::string var_name) override;

  LALogic* lalogic; // Extra var, inner use only - Helps to avoid dynamic cast!

  PTRef ptr_assert_var_constraints;

  unsigned int type_constraints_level; // The level of checks in LRA for numerical checks of overflow
};

#endif
