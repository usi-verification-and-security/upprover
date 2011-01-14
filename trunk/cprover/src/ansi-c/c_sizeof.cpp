/*******************************************************************\

Module: Conversion of sizeof Expressions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <config.h>
#include <arith_tools.h>
#include <simplify_expr.h>
#include <std_expr.h>

#include "c_sizeof.h"
#include "c_typecast.h"
#include "c_types.h"

/*******************************************************************\

Function: c_sizeoft::sizeof_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt c_sizeoft::sizeof_rec(const typet &type)
{
  exprt dest;

  if(type.id()==ID_signedbv ||
     type.id()==ID_unsignedbv ||
     type.id()==ID_floatbv ||
     type.id()==ID_fixedbv)
  {
    unsigned bits=atoi(type.get(ID_width).c_str());
    unsigned bytes=bits/8;
    if((bits%8)!=0) bytes++;
    dest=from_integer(bytes, size_type());
  }
  else if(type.id()==ID_c_enum ||
          type.id()==ID_incomplete_c_enum)
  {
    dest=from_integer(config.ansi_c.int_width/8, size_type());
  }
  else if(type.id()==ID_pointer)
  {
    if(type.get_bool(ID_C_reference))
      return sizeof_rec(type.subtype());
    
    // the following is an MS extension
    if(type.get_bool(ID_C_ptr32))
      return from_integer(4, size_type());

    unsigned bits=config.ansi_c.pointer_width;
    unsigned bytes=bits/8;
    if((bits%8)!=0) bytes++;
    dest=from_integer(bytes, size_type());
  }
  else if(type.id()==ID_bool)
  {
    dest=from_integer(1, size_type());
  }
  else if(type.id()==ID_array)
  {
    const exprt &size_expr=
      static_cast<const exprt &>(type.find(ID_size));

    exprt tmp_dest(sizeof_rec(type.subtype()));

    if(tmp_dest.is_nil())
      return tmp_dest;

    mp_integer a, b;

    if(!to_integer(tmp_dest, a) &&
       !to_integer(size_expr, b))
    {
      dest=from_integer(a*b, size_type());
    }
    else
    {
      dest.id(ID_mult);
      dest.type()=size_type();
      dest.copy_to_operands(size_expr);
      dest.move_to_operands(tmp_dest);
      c_implicit_typecast(dest.op0(), dest.type(), ns);
      c_implicit_typecast(dest.op1(), dest.type(), ns);
    }
  }
  else if(type.id()==ID_incomplete_array)
  {
    // treated like an empty array
    dest=from_integer(0, size_type());
  }
  else if(type.id()==ID_struct)
  {
    const irept::subt &components=
      type.find(ID_components).get_sub();

    dest=from_integer(0, size_type());

    forall_irep(it, components)
    {
      const typet &sub_type=static_cast<const typet &>(it->find(ID_type));

      if(sub_type.id()==ID_code)
      {
      }
      else
      {
        exprt tmp(sizeof_rec(sub_type));

        if(tmp.is_nil())
          return tmp;

        exprt sum=plus_exprt(dest, tmp);
        dest=sum;
      }
    }
  }
  else if(type.id()==ID_union)
  {
    const irept::subt &components=
      type.find(ID_components).get_sub();

    mp_integer max_size=0;

    forall_irep(it, components)
    {
      const typet &sub_type=static_cast<const typet &>(it->find(ID_type));

      if(sub_type.id()==ID_code)
      {
      }
      else
      {
        exprt tmp(sizeof_rec(sub_type));

        if(tmp.is_nil())
          return tmp;
          
        simplify(tmp, ns);

        mp_integer tmp_int;

        if(to_integer(tmp, tmp_int))
          return static_cast<const exprt &>(get_nil_irep());

        if(tmp_int>max_size) max_size=tmp_int;
      }
    }

    dest=from_integer(max_size, size_type());
  }
  else if(type.id()==ID_symbol)
  {
    return sizeof_rec(ns.follow(type));
  }
  else
    dest.make_nil();

  return dest;
}

/*******************************************************************\

Function: c_sizeof

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt c_sizeof(const typet &src, const namespacet &ns)
{
  c_sizeoft c_sizeof_inst(ns);
  exprt tmp=c_sizeof_inst(src);
  simplify(tmp, ns);
  return tmp;
}
