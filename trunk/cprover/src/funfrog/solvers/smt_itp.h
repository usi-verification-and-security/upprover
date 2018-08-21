#ifndef SMT_ITP_H
#define SMT_ITP_H

#include <ostream>
#include <util/std_expr.h>
#include <solvers/prop/literal.h>
#include <solvers/flattening/boolbv.h>

#include <opensmt/opensmt2.h>
#include <opensmt/Tterm.h>
#include "itp.h"
#include "smtcheck_opensmt2.h"

class smt_itpt: public itpt
{
public:
  smt_itpt() = default;
  ~smt_itpt() override = default;

  virtual  bool is_trivial() const override { return false; }

  virtual void print(std::ostream& out) const override;

  virtual void setDecider(check_opensmt2t *_s) override { m_decider = dynamic_cast<smtcheck_opensmt2t *> (_s); assert(m_decider); }
  virtual void setTterm(Tterm& t) override { templ = t; }

  Tterm & getTempl() {return templ;}
  const Tterm & getTemplConst() const {return templ;}

  static void reserve_variables(prop_conv_solvert& decider,
    const std::vector<symbol_exprt>& symbols, std::map<symbol_exprt, std::vector<unsigned> >& symbol_vars);

  void generalize(const prop_conv_solvert& mapping,
    const std::vector<symbol_exprt>& symbols);

  virtual literalt raw_assert(propt& decider) const override;

  // Serialization
  virtual void serialize(std::ostream& out) const override;
  virtual void deserialize(std::istream& in) override;

  virtual bool usesVar(symbol_exprt&, unsigned) override;
  
#ifdef LATTICE_REF_ALGORITHM  
  // KE: FIND BETTER SOLUTION
  std::set<unsigned int> lattice_valid;
#endif

protected:
  typedef std::vector<bvt> clausest;

  // Clauses of the interpolant representation
  clausest clauses;

  // TODO: figure out better way how to store the interpolants
  Tterm templ;

  smtcheck_opensmt2t *m_decider;

    // Mask for used symbols
  std::vector<bool> symbol_mask;

};

typedef smt_itpt smt_interpolantt;
#endif
