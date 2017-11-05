/*******************************************************************\

Module: Propositional interpolant. Based on code of cnft.

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_PROP_ITP_H
#define CPROVER_PROP_ITP_H

#include <iosfwd>
#include <solvers/prop/literal.h>
#include "itp.h"

class symbol_exprt;

class prop_itpt: public itpt
{
public:
  prop_itpt() :itpt() {}
  ~prop_itpt() {} 

  virtual bool is_trivial() const override { return root_literal.is_constant(); }

  virtual literalt land(literalt a, literalt b) override;
  virtual literalt lor(literalt a, literalt b) override;
  virtual literalt lnot(literalt a) override;
  virtual void print(std::ostream& out) const override;

  virtual void setTterm(Tterm& t) override { throw std::logic_error("Propositional interpolator does not deal with terms!"); }
  virtual Tterm* getTterm() override { throw std::logic_error("Propositional interpolator does not deal with terms!"); }
  
  virtual void swap(itpt& other) override {other.swap(*this);}
  virtual void swap(smt_itpt& other) override { throw std::logic_error("Cannot swap PROP and SMT interpolator"); }
  virtual void swap(prop_itpt& other) override {
    clauses.swap(other.clauses);
    std::swap(_no_variables, other._no_variables);
    std::swap(_no_orig_variables, other._no_orig_variables);
    std::swap(root_literal, other.root_literal);
    std::swap(symbol_mask, other.symbol_mask);
    std::swap(valid, other.valid);
  }

  // These 3 methods are needed in partitioning_target_equation (called from)
  static void reserve_variables(prop_conv_solvert& decider,
    		  const std::vector<symbol_exprt>& symbols, std::map<symbol_exprt, 
		  std::vector<unsigned> >& symbol_vars);

  void generalize(const prop_conv_solvert& mapping,
    		  const std::vector<symbol_exprt>& symbols);

  void substitute(prop_conv_solvert& decider,
    const std::vector<symbol_exprt>& symbols,
    bool inverted = false) const;

  virtual literalt raw_assert(propt& decider) const override;

  // Serialization
  virtual void serialize(std::ostream& out) const override;
  virtual void deserialize(std::istream& in) override;

  bool usesVar(symbol_exprt& symb, unsigned idx) override
  { 
      return get_symbol_mask()[idx];
  }
  
  virtual bool check_implies(const itpt& second) const override;
  
  virtual itpt* get_nodet() override { return new prop_itpt(); }

protected:
  typedef std::vector<bvt> clausest;

  // Clauses of the interpolant representation
  clausest clauses;
  
  // Mask for used symbols
  std::vector<bool> symbol_mask;

  void gate_and(literalt a, literalt b, literalt o);
  void gate_or(literalt a, literalt b, literalt o);
  
  void print_clause(std::ostream& out, const bvt& clause) const;

  const std::vector<bool>& get_symbol_mask() const { return symbol_mask; }
};

#endif
