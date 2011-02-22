/*******************************************************************\

Module: Propositional interpolant. Based on code of cnft.

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_PROP_ITP_H
#define CPROVER_PROP_ITP_H

#include <ostream>
#include <solvers/prop/literal.h>

class prop_itpt
{
public:
  prop_itpt() : _no_variables(1) {}

  literalt land(literalt a, literalt b);
  literalt lor(literalt a, literalt b);
  literalt lnot(literalt a);
  unsigned no_variables() const { return _no_variables; }
  unsigned no_clauses() const {return clauses.size(); }
  void print(std::ostream& out) const;

  void swap(prop_itpt& other) {
    clauses.swap(other.clauses);
    std::swap(_no_variables, other._no_variables);
    std::swap(root_literal, other.root_literal);
  }

  literalt new_variable() {
    return literalt(_no_variables++, false);
  }

  // Literal equivalent to the interpolant root
  literalt root_literal;
protected:
  typedef std::vector<bvt> clausest;

  // Number of variables
  unsigned _no_variables;
  // Clauses of the interpolant representation
  clausest clauses;
  // TODO: Mapping from prop. variables to program variables

  void gate_and(literalt a, literalt b, literalt o);
  void gate_or(literalt a, literalt b, literalt o);
};

#endif
