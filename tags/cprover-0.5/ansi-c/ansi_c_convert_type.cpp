/*******************************************************************\

Module: SpecC Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <iostream>

#include <config.h>
#include <arith_tools.h>
#include <std_types.h>

#include "ansi_c_convert_type.h"

/*******************************************************************\

Function: ansi_c_convert_typet::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_convert_typet::read(const typet &type)
{
  clear();
  location=type.location();
  read_rec(type);
}

/*******************************************************************\

Function: ansi_c_convert_typet::read_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_convert_typet::read_rec(const typet &type)
{
  if(type.id()==ID_merged_type)
  {
    forall_subtypes(it, type)
      read_rec(*it);
  }
  else if(type.id()==ID_signed)
    signed_cnt++;
  else if(type.id()==ID_unsigned)
    unsigned_cnt++;
  else if(type.id()==ID_ptr32)
    c_qualifiers.is_ptr32=true;
  else if(type.id()==ID_ptr64)
    c_qualifiers.is_ptr64=true;
  else if(type.id()==ID_volatile)
    c_qualifiers.is_volatile=true;
  else if(type.id()==ID_const)
    c_qualifiers.is_constant=true;
  else if(type.id()==ID_restricted)
    c_qualifiers.is_restricted=true;
  else if(type.id()==ID_char)
    char_cnt++;
  else if(type.id()==ID_int)
    int_cnt++;
  else if(type.id()==ID_int8)
    int8_cnt++;
  else if(type.id()==ID_int16)
    int16_cnt++;
  else if(type.id()==ID_int32)
    int32_cnt++;
  else if(type.id()==ID_int64)
    int64_cnt++;
  else if(type.id()==ID_short)
    short_cnt++;
  else if(type.id()==ID_long)
    long_cnt++;
  else if(type.id()==ID_double)
    double_cnt++;
  else if(type.id()==ID_float)
    float_cnt++;
  else if(type.id()==ID_bool)
    bool_cnt++;
  else if(type.id()==ID_static)
    c_storage_spec.is_static=true;
  else if(type.id()==ID_thread_local)
    c_storage_spec.is_thread_local=true;
  else if(type.id()==ID_inline)
    c_storage_spec.is_inline=true;
  else if(type.id()==ID_extern)
    c_storage_spec.is_extern=true;
  else if(type.id()==ID_typedef)
    c_storage_spec.is_typedef=true;
  else if(type.id()==ID_register)
    c_storage_spec.is_register=true;
  else if(type.id()==ID_auto)
  {
    // ignore
  }
  else if(type.id()==ID_packed)
    packed=true;
  else if(type.id()==ID_aligned)
    aligned=true;
  else if(type.id()==ID_transparent_union)
    transparent_union=true;
  else if(type.id()==ID_vector)
    vector_size=to_vector_type(type).size();
  else 
    other.push_back(type);
}

/*******************************************************************\

Function: ansi_c_convert_typet::write

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_convert_typet::write(typet &type)
{
  type.clear();
  
  // first, do "other"

  if(!other.empty())
  {
    if(double_cnt || float_cnt || signed_cnt ||
       unsigned_cnt || int_cnt || bool_cnt ||
       short_cnt || char_cnt ||
       int8_cnt || int16_cnt || int32_cnt || int64_cnt ||
       long_cnt)
    {
      err_location(location);
      error("illegal type modifier for defined type");
      throw 0;
    }

    if(other.size()!=1)
    {
      err_location(location);
      error("illegal combination of defined types");
      throw 0;
    }

    type.swap(other.front());
  }
  else if(double_cnt || float_cnt)
  {
    if(signed_cnt || unsigned_cnt || int_cnt || bool_cnt ||
       int8_cnt || int16_cnt || int32_cnt || int64_cnt ||
       short_cnt || char_cnt)
    {
      err_location(location);
      error("cannot combine integer type with float");
      throw 0;
    }

    if(double_cnt && float_cnt)
    {
      err_location(location);
      error("conflicting type modifiers");
      throw 0;
    }

    if(long_cnt==0)
    {
      if(double_cnt!=0)
        type=double_type();
      else
        type=float_type();
    }
    else if(long_cnt==1 || long_cnt==2)
    {
      if(double_cnt!=0)
        type=long_double_type();
      else
      {
        err_location(location);
        error("conflicting type modifiers");
        throw 0;
      }
    }
    else
    {
      err_location(location);
      error("illegal type modifier for float");
      throw 0;
    }
  }
  else if(bool_cnt)
  {
    if(signed_cnt || unsigned_cnt || int_cnt || short_cnt ||
       int8_cnt || int16_cnt || int32_cnt || int64_cnt ||
       char_cnt || long_cnt)
    {
      err_location(location);
      error("illegal type modifier for boolean type");
      throw 0;
    }

    type.id(ID_bool);
  }
  else
  {
    // it is integer -- signed or unsigned?

    if(signed_cnt && unsigned_cnt)
    {
      err_location(location);
      error("conflicting type modifiers");
      throw 0;
    }
    else if(unsigned_cnt)
      type.id(ID_unsignedbv);
    else if(signed_cnt)
      type.id(ID_signedbv);
    else
    {
      if(char_cnt)
        type.id(config.ansi_c.char_is_unsigned?ID_unsignedbv:ID_signedbv);
      else
        type.id(ID_signedbv);
    }

    // get width

    unsigned width;

    if(int8_cnt || int16_cnt || int32_cnt || int64_cnt)
    {
      if(long_cnt || char_cnt || short_cnt)
      {
        err_location(location);
        error("conflicting type modifiers");
        throw 0;
      }
      
      if(int8_cnt)
        width=1*8;
      else if(int16_cnt)
        width=2*8;
      else if(int32_cnt)
        width=4*8;
      else if(int64_cnt)
        width=8*8;
      else
        assert(false);
    }
    else if(short_cnt)
    {
      if(long_cnt || char_cnt)
      {
        err_location(location);
        error("conflicting type modifiers");
        throw 0;
      }

      width=config.ansi_c.short_int_width;
    }
    else if(char_cnt)
    {
      if(long_cnt)
      {
        err_location(location);
        error("illegal type modifier for char type");
        throw 0;
      }

      width=config.ansi_c.char_width;
    }
    else if(long_cnt==0)
    {
      width=config.ansi_c.int_width;
    }
    else if(long_cnt==1)
    {
      width=config.ansi_c.long_int_width;
    }
    else if(long_cnt==2)
    {
      width=config.ansi_c.long_long_int_width;
    }
    else
    {
      err_location(location);
      error("illegal type modifier for integer type");
      throw 0;
    }

    type.set(ID_width, width);
  }

  if(vector_size.is_not_nil())
  {
    vector_typet new_type;
    new_type.size()=vector_size;
    new_type.location()=vector_size.location();
    new_type.subtype().swap(type);
    type=new_type;
  }

  c_qualifiers.write(type);

  if(transparent_union)
    type.set(ID_transparent_union, true);

  if(packed && type.id()==ID_struct)
    type.set(ID_packed, true);

  if(aligned)
    type.set(ID_aligned, true);
}
