#ifndef ITP_H
#define ITP_H

#include <solvers/prop/literal.h>
#include <opensmt/PTRef.h>
#include <util/symbol.h>

class itpt
{
public:
  itpt() : interpolant{PTRef_Undef} {}
  virtual ~itpt() {} // d'tor

  virtual bool is_trivial() const =0;

  // New for OpenSMT code
  virtual bool usesVar(symbol_exprt&, unsigned) = 0;

  // Serialization
  virtual void serialize(std::ostream& out) const = 0;

  virtual bool equals(itpt* other) const = 0;

  // Getters & Setters
  PTRef getInterpolant() const { return interpolant; }
  void setInterpolant(PTRef pt) { interpolant = pt; }

protected:
  PTRef interpolant;

};

#endif
