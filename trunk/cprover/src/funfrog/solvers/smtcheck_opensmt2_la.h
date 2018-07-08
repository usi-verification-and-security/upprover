/*******************************************************************\

Module: Wrapper for OpenSMT2

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_OPENSMT2_LA_H
#define CPROVER_SMTCHECK_OPENSMT2_LA_H

#include "smtcheck_opensmt2.h"

class smtcheck_opensmt2t_la : public smtcheck_opensmt2t
{
public:
  smtcheck_opensmt2t_la(int _type_constraints_level, const char* name, bool _store_unsupported_info=false) :
          smtcheck_opensmt2t(false, 3, 2, _store_unsupported_info),
          type_constraints_level(_type_constraints_level)
  { } // Virtual class
      
  virtual ~smtcheck_opensmt2t_la(); // d'tor

  virtual exprt get_value(const exprt &expr) override;

  virtual literalt convert(const exprt &expr) override;

  virtual literalt const_from_str(const char* num);

  virtual literalt const_var_Number(const exprt &expr) override;

  //virtual literalt type_cast(const exprt &expr)=0;
  
  virtual literalt labs(const exprt &expr)=0;
  
  virtual literalt lnotequal(literalt l1, literalt l2) override;

  // for isnan, mod, arrays etc. that we have no support (or no support yet) create over-approx as nondet
  virtual literalt lunsupported2var(const exprt &expr) override;

  virtual literalt lvar(const exprt &expr) override;
    
  virtual literalt lassert_var() override
	{ literalt l; l = smtcheck_opensmt2t::push_variable(ptr_assert_var_constraints); return l;}

  //virtual std::string getStringSMTlibDatatype(const typet& type)=0;
  //virtual SRef getSMTlibDatatype(const typet& type)=0;
  
// KE: FIXME remove this code till the end of the endif after OpenSMT has support for LA interpolation
#ifdef PRODUCE_PROOF
  virtual void get_interpolant(const interpolation_taskt& partition_ids,
      interpolantst& interpolants) override {assert(0);}

  virtual bool can_interpolate() const override {assert(0);}

  // Extract interpolant form OpenSMT files/data
  virtual void extract_itp(PTRef ptref, smt_itpt& target_itp) const override {assert(0);}

  virtual void generalize_summary(smt_itpt& interpolant, std::vector<symbol_exprt>& common_symbols,
                          const std::string& fun_name, bool substitute) override {assert(0);}
#endif  

protected:
  LALogic* lalogic; // Extra var, inner use only - Helps to avoid dynamic cast!

  PTRef ptr_assert_var_constraints;

  int type_constraints_level; // The level of checks in LA for numerical checks of overflow

  //virtual void initializeSolver(const char*)=0;

  PTRef mult_numbers(const exprt &expr, vec<PTRef> &args);

  PTRef div_numbers(const exprt &expr, vec<PTRef> &args);

  PTRef runsupported2var(const exprt &expr);

  bool isLinearOp(const exprt &expr, vec<PTRef> &args); // Check if we don't do sth. like nondet*nondet, but only const*nondet (e.g.)

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
};

#endif
