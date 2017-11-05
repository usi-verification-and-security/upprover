#ifndef ITP_H
#define ITP_H

#include <ostream>
#include <std_expr.h>
#include <solvers/prop/literal.h>
#include <solvers/flattening/boolbv.h>
#include <opensmt/opensmt2.h>
#include <opensmt/Tterm.h>

class prop_itpt;
class smt_itpt;

class itpt
{
public:
  itpt() : logic(nullptr), _no_variables(1), _no_orig_variables(1) {}
  virtual ~itpt() {} // d'tor

  virtual bool is_trivial() const =0;

  virtual literalt land(literalt a, literalt b) =0;
  virtual literalt lor(literalt a, literalt b)=0;
  virtual literalt lnot(literalt a)=0;
  virtual void swap(itpt& other)=0;
  virtual void swap(prop_itpt& other)=0;
  virtual void swap(smt_itpt& other)=0;
  
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
  virtual Tterm* getTterm() =0; // moved to smt_itp { return tterm; }
  
  void setInterpolant(PTRef pt) { interpolant = pt; }
  virtual void setTterm(Tterm& t) =0; // moved to smt_itp { tterm = &t; }
  void setLogic(Logic *_l) { logic = _l; }

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
  Logic *logic;

  bool valid;

  // Number of all used variables
  unsigned _no_variables;

  // Upper bound on the number of variables in the interpolant. Variables with
  // a higher number are due to Tseitin encoding
  unsigned _no_orig_variables;
};

#endif
