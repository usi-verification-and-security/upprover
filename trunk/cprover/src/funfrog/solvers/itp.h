#ifndef ITP_H
#define ITP_H

#include <util/std_expr.h>
#include <solvers/prop/literal.h>
#include <solvers/flattening/boolbv.h>
#include <opensmt/PTRef.h>

class prop_itpt;
class smt_itpt;

class itpt
{
public:
  itpt() :_no_variables(1), _no_orig_variables(1) {}
  virtual ~itpt() {} // d'tor

  virtual bool is_trivial() const =0;

  virtual itpt* get_nodet() =0;

  // For SAT & SMT code
  literalt new_variable() {
    return literalt(_no_variables++, false);
  }

  // Old for SAT code
  virtual literalt raw_assert(propt& decider) const=0;
  virtual void print(std::ostream& out) const=0;

  // New for OpenSMT code
  virtual bool usesVar(symbol_exprt&, unsigned)=0;
  
  
  // Serialization
  virtual void serialize(std::ostream& out) const=0;
  virtual void deserialize(std::istream& in)=0;
  
  virtual bool check_implies(const itpt& second) const=0;

  // Getters & Setters
  PTRef getInterpolant() { return interpolant; }
  void setInterpolant(PTRef pt) { interpolant = pt; }


  bool is_valid(){ return valid; };
  void set_valid(bool _valid){ valid = _valid; };

  unsigned no_variables() const { return _no_variables; }
  void set_no_original_variables(unsigned no) { 
    _no_variables = no; _no_orig_variables = no;
  }

  // Literal equivalent to the interpolant root
  literalt root_literal;
protected:
  PTRef interpolant;

  bool valid;

  // Number of all used variables
  unsigned _no_variables;

  // Upper bound on the number of variables in the interpolant. Variables with
  // a higher number are due to Tseitin encoding
  unsigned _no_orig_variables;
};

#endif
