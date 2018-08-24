#ifndef SMT_ITP_H
#define SMT_ITP_H

#include "itp.h"

#include <opensmt/Tterm.h>
#include <iosfwd>

class smtcheck_opensmt2t;

class smt_itpt: public itpt
{
public:
  smt_itpt() = default;
  ~smt_itpt() override = default;

  virtual  bool is_trivial() const override { return false; }

  void setDecider(check_opensmt2t *_s);
  void setTterm(Tterm& t) { templ = t; }

  Tterm & getTempl() {return templ;}
  const Tterm & getTempl() const {return templ;}

  // Serialization
  virtual void serialize(std::ostream& out) const override;

  bool equals(itpt* other) const override;

protected:
  // TODO: figure out better way how to store the interpolants
  Tterm templ;

  smtcheck_opensmt2t *m_decider;

};

typedef smt_itpt smt_interpolantt;
#endif
