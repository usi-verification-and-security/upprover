/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_NAMESPACE_SPEC_H
#define CPROVER_CPP_NAMESPACE_SPEC_H

#include <expr.h>

class cpp_namespace_spect:public exprt
{
public:
  cpp_namespace_spect():exprt("cpp-namespace-spec")
  {
  }
  
  typedef std::vector<class cpp_itemt> itemst;

  const itemst &items() const
  {
    return (const itemst &)operands();
  }

  itemst &items()
  {
    return (itemst &)operands();
  }
  
  const irep_idt &get_namespace() const
  {
    return get("namespace");
  }

  void set_namespace(const irep_idt &_namespace)
  {
    set("namespace", _namespace);
  }
  
  void output(std::ostream &out) const;
};

#endif