/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_DECLARATION_H
#define CPROVER_CPP_DECLARATION_H

#include <assert.h>

#include "cpp_declarator.h"
#include "cpp_storage_spec.h"
#include "cpp_member_spec.h"

class cpp_declarationt:public exprt
{
public:
  typedef std::vector<cpp_declaratort> declaratorst;

  cpp_declarationt():exprt("cpp-declaration")
  {
  }
  
  bool is_template() const
  {
    return get_bool(ID_is_template);
  }
  
  const declaratorst &declarators() const
  {
    return (const declaratorst &)operands();
  }

  declaratorst &declarators()
  {
    return (declaratorst &)operands();
  }
  
  const cpp_storage_spect &storage_spec() const
  {
    return static_cast<const cpp_storage_spect &>(
      find("storage_spec"));
  }

  cpp_storage_spect &storage_spec()
  {
    return static_cast<cpp_storage_spect &>(
      add("storage_spec"));
  }

  const cpp_member_spect &member_spec() const
  {
    return static_cast<const cpp_member_spect &>(
      find("member_spec"));
  }

  cpp_member_spect &member_spec()
  {
    return static_cast<cpp_member_spect &>(
      add("member_spec"));
  }

  typet &template_type()
  {
    return static_cast<typet &>(add(ID_template_type));
  }

  const typet &template_type() const
  {
    return static_cast<const typet &>(find(ID_template_type));
  }

  void output(std::ostream &out) const;
};

extern inline cpp_declarationt &to_cpp_declaration(irept &irep)
{
  assert(irep.id()=="cpp-declaration");
  return static_cast<cpp_declarationt &>(irep);
}

extern inline const cpp_declarationt &to_cpp_declaration(const irept &irep)
{
  assert(irep.id()=="cpp-declaration");
  return static_cast<const cpp_declarationt &>(irep);
}

#endif
