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
class prop_conv_solvert;

class prop_itpt: public itpt
{
public:
    typedef std::vector<bvt> clausest;

  prop_itpt() :itpt(), _no_variables(1), _no_orig_variables(1) {}
  ~prop_itpt() {} 

  virtual bool is_trivial() const override { return root_literal.is_constant(); }

  literalt land(literalt a, literalt b);
  literalt lor(literalt a, literalt b);
  literalt lnot(literalt a);
  void print(std::ostream& out) const;

  // Serialization
  virtual void serialize(std::ostream& out) const override;
  void deserialize(std::istream& in);

  bool usesVar(symbol_exprt& symb, unsigned idx) override
  { 
      return get_symbol_mask()[idx];
  }

  const clausest & get_clauses() const {return clauses;}
  clausest & get_clauses() {return clauses;}

    literalt new_variable() {
        return literalt(_no_variables++, false);
    }

    std::vector<bool>& get_symbol_mask() { return symbol_mask; }

    literalt get_root_literal() const {return root_literal;}
    void set_root_literal(literalt new_root) {root_literal = new_root;}

    unsigned get_no_variables() const { return _no_variables; }

    void set_no_original_variables(unsigned no) {
        _no_orig_variables = no;
    }

    void set_no_variables(unsigned no) {
        _no_variables = no;
    }

    unsigned get_no_original_variables() const {return _no_orig_variables;}

protected:
  // Clauses of the interpolant representation
  clausest clauses;
  
  // Mask for used symbols
  std::vector<bool> symbol_mask;

    // Literal equivalent to the interpolant root
    literalt root_literal;

    // Number of all used variables
    unsigned _no_variables;

    // Upper bound on the number of variables in the interpolant. Variables with
    // a higher number are due to Tseitin encoding
    unsigned _no_orig_variables;

  void gate_and(literalt a, literalt b, literalt o);
  void gate_or(literalt a, literalt b, literalt o);
  
  void print_clause(std::ostream& out, const bvt& clause) const;

  const std::vector<bool>& get_symbol_mask() const { return symbol_mask; }
};

#endif
