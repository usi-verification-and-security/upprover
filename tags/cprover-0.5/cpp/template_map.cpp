/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include "template_map.h"

/*******************************************************************\

Function: template_mapt::apply

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_mapt::apply(typet &type) const
{
  if(type.id()==ID_array)
  {
    apply(type.subtype());
    apply(static_cast<exprt &>(type.add(ID_size)));
  }
  else if(type.id()==ID_pointer)
  {
    apply(type.subtype());
  }
  else if(type.id()==ID_struct ||
          type.id()==ID_union)
  {
    irept::subt &components=type.add(ID_components).get_sub();

    Forall_irep(it, components)
    {
      typet &subtype=static_cast<typet &>(it->add(ID_type));
      apply(subtype);
    }
  }
  else if(type.id()==ID_symbol)
  {
    type_mapt::const_iterator m_it=
      type_map.find(type.get(ID_identifier));

    if(m_it!=type_map.end())
    {
      type=m_it->second;
      return;
    }
  }
  else if(type.id()==ID_code)
  {
    apply(static_cast<typet &>(type.add(ID_return_type)));

    irept::subt &arguments=type.add(ID_arguments).get_sub();

    Forall_irep(it, arguments)
    {
      if(it->id()==ID_argument)
        apply(static_cast<typet &>(it->add(ID_type)));
    }
  }
  else if(type.id()==ID_merged_type)
  {
    Forall_subtypes(it, type)
      apply(*it);
  }
}

/*******************************************************************\

Function: template_mapt::apply

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_mapt::apply(exprt &expr) const
{
  apply(expr.type());

  if(expr.id()==ID_symbol)
  {
    expr_mapt::const_iterator m_it=
      expr_map.find(expr.get(ID_identifier));

    if(m_it!=expr_map.end())
    {
      expr=m_it->second;
      return;
    }
  }

  Forall_operands(it, expr)
    apply(*it);
}

/*******************************************************************\

Function: template_mapt::apply

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt template_mapt::lookup(const irep_idt &identifier) const
{
  type_mapt::const_iterator t_it=
    type_map.find(identifier);

  if(t_it!=type_map.end())
  {
    exprt e(ID_type);
    e.type()=t_it->second;
    return e;
  }

  expr_mapt::const_iterator e_it=
    expr_map.find(identifier);

  if(e_it!=expr_map.end())
    return e_it->second;

  return static_cast<const exprt &>(get_nil_irep());
}

/*******************************************************************\

Function: template_mapt::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_mapt::print(std::ostream &out) const
{
  for(type_mapt::const_iterator it=type_map.begin();
      it!=type_map.end();
      it++)
    out << it->first << " = " << it->second.pretty() << std::endl;

  for(expr_mapt::const_iterator it=expr_map.begin();
      it!=expr_map.end();
      it++)
    out << it->first << " = " << it->second.pretty() << std::endl;
}

