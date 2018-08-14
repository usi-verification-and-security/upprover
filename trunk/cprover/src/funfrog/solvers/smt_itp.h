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
  smt_itpt() = default;
  ~smt_itpt() override = default;

  virtual  bool is_trivial() const override { return false; }

  void setLogic(Logic *_l) { logic = _l; }

  const Tterm & getTempl() const {return templ;}
  Tterm & getTempl() {return templ;}

  // Serialization
  virtual void serialize(std::ostream& out) const override;

  virtual bool usesVar(symbol_exprt&, unsigned) override;

  bool equals(itpt* other) const override;

protected:
  // TODO: figure out better way how to store the interpolants
  Tterm templ;

  Logic *logic;

};

typedef smt_itpt smt_interpolantt;
#endif
