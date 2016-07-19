#ifndef SMT_ITP_H
#define SMT_ITP_H

#include <ostream>
#include <std_expr.h>
#include <solvers/prop/literal.h>
#include <solvers/flattening/boolbv.h>

#include <opensmt/opensmt2.h>
#include <opensmt/Tterm.h>

class smt_itpt
{
public:
  smt_itpt() : _no_variables(1), _no_orig_variables(1) {}

  bool is_trivial() const { return root_literal.is_constant(); };

  literalt land(literalt a, literalt b);
  literalt lor(literalt a, literalt b);
  literalt lnot(literalt a);
  unsigned no_variables() const { return _no_variables; }
  unsigned no_clauses() const {return clauses.size(); }
  void set_no_original_variables(unsigned no) { 
    _no_variables = no; _no_orig_variables = no;
  }
  void print(std::ostream& out) const;

  void swap(smt_itpt& other) {
    clauses.swap(other.clauses);
    std::swap(_no_variables, other._no_variables);
    std::swap(_no_orig_variables, other._no_orig_variables);
    std::swap(root_literal, other.root_literal);
    std::swap(symbol_mask, other.symbol_mask);
    std::swap(valid, other.valid);
  }

  literalt new_variable() {
    return literalt(_no_variables++, false);
  }

  static void reserve_variables(prop_convt& decider,
    const std::vector<symbol_exprt>& symbols, std::map<symbol_exprt, std::vector<unsigned> >& symbol_vars);

  void generalize(const prop_convt& mapping,
    const std::vector<symbol_exprt>& symbols);

  void substitute(prop_convt& decider,
    const std::vector<symbol_exprt>& symbols,
    bool inverted = false) const;

  literalt raw_assert(propt& decider) const;
  
  const std::vector<bool>& get_symbol_mask() const { return symbol_mask; }

  // Serialization
  void serialize(std::ostream& out) const;
  void deserialize(std::istream& in);

  // Literal equivalent to the interpolant root
  literalt root_literal;

  bool is_valid(){ return valid; };

  void set_valid(bool _valid){ valid = _valid; };

  PTRef getInterpolant() { return interpolant; }
  void setInterpolant(PTRef pt) { interpolant = pt; }
  void setTterm(Tterm *t) { tterm = t; }

protected:
  bool valid;

  typedef std::vector<bvt> clausest;

  // Number of all used variables
  unsigned _no_variables;
  // Upper bound on the number of variables in the interpolant. Variables with
  // a higher number are due to Tseitin encoding
  unsigned _no_orig_variables;

  // Clauses of the interpolant representation
  clausest clauses;
  
  // Mask for used symbols
  std::vector<bool> symbol_mask;

  void gate_and(literalt a, literalt b, literalt o);
  void gate_or(literalt a, literalt b, literalt o);
  
  void print_clause(std::ostream& out, const bvt& clause) const;

  PTRef interpolant;
  Tterm *tterm;
};

typedef smt_itpt interpolantt;
typedef std::vector<smt_itpt> interpolantst;

#endif
