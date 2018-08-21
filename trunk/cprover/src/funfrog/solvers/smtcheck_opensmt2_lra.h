/*******************************************************************\

Module: Wrapper for OpenSMT2

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_OPENSMT2_LRA_H
#define CPROVER_SMTCHECK_OPENSMT2_LRA_H

#include "smtcheck_opensmt2_la.h"

class smtcheck_opensmt2t_lra : public smtcheck_opensmt2t_la
{
public:
  smtcheck_opensmt2t_lra(unsigned int _type_constraints_level, const char* name, bool _store_unsupported_info=false) :
          smtcheck_opensmt2t_la(_type_constraints_level, name, _store_unsupported_info)
  {
    initializeSolver(name);
  }
      
  virtual ~smtcheck_opensmt2t_lra(); // d'tor

  virtual literalt type_cast(const exprt &expr) override;
  
  virtual literalt labs(const exprt &expr) override; // from convert for ID_abs

  void check_ce(std::vector<exprt>& exprs); // checking spuriousness of the error trace (not refinement here)
  
  virtual std::string getStringSMTlibDatatype(const typet& type) override;
  virtual SRef getSMTlibDatatype(const typet& type) override;

protected:
  virtual void initializeSolver(const char*) override;

};

#endif
