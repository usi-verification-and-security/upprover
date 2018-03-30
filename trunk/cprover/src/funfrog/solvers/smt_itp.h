#ifndef SMT_ITP_H
#define SMT_ITP_H

#include <ostream>
#include <util/std_expr.h>
#include <solvers/prop/literal.h>
#include <solvers/flattening/boolbv.h>

#include <opensmt/opensmt2.h>
#include <opensmt/Tterm.h>
#include "itp.h"

class smt_itpt: public itpt
{
public:
  smt_itpt() :tterm(nullptr){}
  ~smt_itpt() {} // d'tor

  virtual  bool is_trivial() const override { return false; }

  virtual literalt land(literalt a, literalt b) override;
  virtual literalt lor(literalt a, literalt b) override;
  virtual literalt lnot(literalt a) override;
  virtual void print(std::ostream& out) const override;

  virtual void setTterm(Tterm& t) override { tterm = &t; }
  virtual Tterm* getTterm() override { return tterm; }
  
  virtual void swap(itpt& other) override {other.swap(*this);}
  virtual void swap(prop_itpt& other) override { throw std::logic_error("Cannot swap SMT and PROP interpolator!"); }
  virtual void swap(smt_itpt& other) override {
    clauses.swap(other.clauses);
    std::swap(_no_variables, other._no_variables);
    std::swap(_no_orig_variables, other._no_orig_variables);
    std::swap(root_literal, other.root_literal);
    std::swap(symbol_mask, other.symbol_mask);
    std::swap(valid, other.valid);
    std::swap(tterm, other.tterm);
    std::swap(logic, other.logic);
    std::swap(interpolant, other.interpolant);
  }

  static void reserve_variables(prop_conv_solvert& decider,
    const std::vector<symbol_exprt>& symbols, std::map<symbol_exprt, std::vector<unsigned> >& symbol_vars);

  void generalize(const prop_conv_solvert& mapping,
    const std::vector<symbol_exprt>& symbols);

//  void substitute(smtcheck_opensmt2t& decider,
//    const std::vector<symbol_exprt>& symbols,
//    bool inverted = false) const;

  virtual literalt raw_assert(propt& decider) const override;

  // Serialization
  virtual void serialize(std::ostream& out) const override;
  virtual void deserialize(std::istream& in) override;

  virtual bool usesVar(symbol_exprt&, unsigned) override;

  virtual bool check_implies(const itpt& second) const override { return false;}
  
  virtual itpt* get_nodet() override { return new smt_itpt(); }

protected:
  typedef std::vector<bvt> clausest;

  // Clauses of the interpolant representation
  clausest clauses;
  
  // Only for SMT version
  Tterm *tterm;
  
  // Mask for used symbols
  std::vector<bool> symbol_mask;

  void gate_and(literalt a, literalt b, literalt o);
  void gate_or(literalt a, literalt b, literalt o);
};

typedef smt_itpt smt_interpolantt;
#endif
