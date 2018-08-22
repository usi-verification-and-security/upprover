/*******************************************************************\

Module: Wrapper for OpenSMT2

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_OPENSMT2_LIA_H
#define CPROVER_SMTCHECK_OPENSMT2_LIA_H

#include "smtcheck_opensmt2_la.h"

class smtcheck_opensmt2t_lia : public smtcheck_opensmt2t_la
{
public:
  smtcheck_opensmt2t_lia(unsigned int _type_constraints_level, const char* name) :
          smtcheck_opensmt2t_la(_type_constraints_level, name)
  {
    initializeSolver(name);
    ptr_assert_var_constraints = logic->getTerm_true();
  }
      
  virtual ~smtcheck_opensmt2t_lia(); // d'tor

  virtual std::string getStringSMTlibDatatype(const typet& type) override;
  virtual SRef getSMTlibDatatype(const typet& type) override;

#ifdef PRODUCE_PROOF
  virtual bool can_interpolate() const override {return false;}

  // Extract interpolant form OpenSMT files/data
  virtual void extract_itp(PTRef ptref, smt_itpt& target_itp) const override {assert(0);}

#endif
protected:

  virtual void initializeSolver(const char*) override;
  
};

#endif
