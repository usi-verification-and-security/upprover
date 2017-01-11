/*******************************************************************\

Module: Propositional interpolant. Based on code of cnft.

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_PROP_ITP_H
#define CPROVER_PROP_ITP_H

#include <ostream>
#include <std_expr.h>
#include <solvers/prop/literal.h>
#include <solvers/flattening/boolbv.h>
#include "itp.h"
#include "satcheck_opensmt2.h"

class prop_itpt: public itpt
{
public:
  prop_itpt() :itpt() {}
  ~prop_itpt() {} 

  virtual bool is_trivial() const { return root_literal.is_constant(); }

  virtual literalt land(literalt a, literalt b);
  virtual literalt lor(literalt a, literalt b);
  virtual literalt lnot(literalt a);
  virtual void print(std::ostream& out) const;

  virtual void swap(itpt& other) {other.swap(*this);}
  virtual void swap(smt_itpt& other) override {assert(0);}
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

  virtual literalt raw_assert(propt& decider) const;

  // Serialization
  virtual void serialize(std::ostream& out) const;
  virtual void deserialize(std::istream& in);

  virtual bool usesVar(symbol_exprt& symb, unsigned idx) 
  { 
      return get_symbol_mask()[idx];
  }
  
  virtual bool check_implies(const itpt& second) const;

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

typedef prop_itpt prop_interpolantt;

#endif
