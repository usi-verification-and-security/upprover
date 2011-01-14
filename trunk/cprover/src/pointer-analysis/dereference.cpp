/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <expr_util.h>
#include <c_misc.h>
#include <base_type.h>
#include <arith_tools.h>
#include <rename.h>
#include <i2string.h>
#include <array_name.h>
#include <config.h>
#include <std_expr.h>
#include <cprover_prefix.h>
#include <pointer_offset_size.h>

#include <ansi-c/c_types.h>
#include <ansi-c/c_typecast.h>

#include <goto-programs/dynamic_memory.h>
#include <pointer-analysis/value_set.h>

#include <langapi/language_util.h>

#include "dereference.h"
#include "pointer_offset_sum.h"

// global data, horrible
unsigned int dereferencet::invalid_counter=0;

/*******************************************************************\

Function: dereferencet::has_dereference

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool dereferencet::has_dereference(const exprt &expr) const
{
  forall_operands(it, expr)
    if(has_dereference(*it))
      return true;

  if(expr.id()==ID_dereference)
    return true;

  // we no longer do this one
  if(expr.id()==ID_index &&
     expr.operands().size()==2 &&
     expr.op0().type().id()==ID_pointer)
    assert(false);  

  return false;
}

/*******************************************************************\

Function: dereferencet::get_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const exprt &dereferencet::get_symbol(const exprt &expr)
{
  if(expr.id()==ID_member || expr.id()==ID_index)
    return get_symbol(expr.op0());
  
  return expr;
}

/*******************************************************************\

Function: dereferencet::dereference

  Inputs: expression dest, to be dereferenced under given guard,
          and given mode

 Outputs: returns pointer after dereferencing

 Purpose:

\*******************************************************************/

exprt dereferencet::dereference(
  const exprt &pointer,
  const guardt &guard,
  const modet mode)
{
  if(pointer.type().id()!=ID_pointer)
    throw "dereference expected pointer type, but got "+
          pointer.type().pretty();  
  
  // type of the object
  const typet &type=pointer.type().subtype();

  #if 0
  std::cout << "DEREF: " << dest.pretty() << std::endl;
  #endif

  // collect objects the pointer may point to
  value_setst::valuest points_to_set;
  
  dereference_callback.get_value_set(pointer, points_to_set);

  // now build big case split
  // only "good" objects

  exprt value=nil_exprt();
  
  for(value_setst::valuest::const_iterator
      it=points_to_set.begin();
      it!=points_to_set.end();
      it++)
  {
    exprt new_value, pointer_guard;
    
    build_reference_to(
      *it, mode, pointer, guard,
      new_value, pointer_guard);
      
    if(new_value.is_not_nil())
    {
      if(value.is_nil())
        value=new_value;
      else
      {
        if_exprt tmp;
        tmp.type()=type;
        tmp.cond()=pointer_guard;
        tmp.true_case()=new_value;
        tmp.false_case().swap(value);
        value.swap(tmp);
      }
    }
  }

  if(value.is_nil())
  {
    if(options.get_bool_option("pointer-check"))
    {
      dereference_callback.dereference_failure(
        "pointer dereference",
        "invalid pointer", guard);
    }

    // first see if we have a "failed object" for this pointer
    
    const symbolt *failed_symbol;

    if(dereference_callback.has_failed_symbol(
         pointer, failed_symbol))
    {
      // yes!
      value=symbol_expr(*failed_symbol);
    }
    else
    {
      // else, do new symbol

      symbolt symbol;
      symbol.name="symex::invalid_object"+i2string(invalid_counter++);
      symbol.base_name="invalid_object";
      symbol.type=type;

      // make it a lvalue, so we can assign to it
      symbol.lvalue=true;
      
      get_new_name(symbol, ns);

      value=symbol_expr(symbol);
      
      new_context.move(symbol);
    }
    
    value.set("#invalid_object", true);
  }

  return value;
}

/*******************************************************************\

Function: dereferencet::add_checks

  Inputs: expression to be checked under guard and mode

 Outputs:

 Purpose: add pointer safety checks for given expression

\*******************************************************************/

void dereferencet::add_checks(
  const exprt &pointer,
  const guardt &guard,
  const modet mode)
{
  if(pointer.type().id()!=ID_pointer)
    throw "dereference expected pointer type, but got "+
          pointer.type().pretty();

  #if 0
  std::cout << "ADD CHECK: " << pointer.pretty() << std::endl;
  #endif

  // collect objects the pointer may point to
  value_setst::valuest points_to_set;

  dereference_callback.get_value_set(pointer, points_to_set);
  
  // if it's empty, we have a problem
  if(points_to_set.empty())
  {
    if(options.get_bool_option("pointer-check"))
    {
      dereference_callback.dereference_failure(
        "pointer dereference",
        "invalid pointer", guard);
    }
  }
  else
  {
    for(value_setst::valuest::const_iterator
        it=points_to_set.begin();
        it!=points_to_set.end();
        it++)
    {
      exprt new_value, pointer_guard;

      build_reference_to(
        *it, mode, pointer, guard,
        new_value, pointer_guard);
    }
  }
}

/*******************************************************************\

Function: dereferencet::dereference_type_compare

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool dereferencet::dereference_type_compare(
  const typet &object_type,
  const typet &dereference_type) const
{
  if(dereference_type.id()==ID_empty)
    return true; // always ok

  if(base_type_eq(object_type, dereference_type, ns))
    return true; // ok, they just match

  // check for struct prefixes

  const typet ot_base=ns.follow(object_type),
              dt_base=ns.follow(dereference_type);

  if(ot_base.id()==ID_struct &&
     dt_base.id()==ID_struct)
  {
    if(to_struct_type(dt_base).is_prefix_of(
         to_struct_type(ot_base)))
      return true; // ok, dt is a prefix of ot
  }
  
  // we are generous about code pointers
  if(dereference_type.id()==ID_code &&
     object_type.id()==ID_code)
    return true;

  // really different

  return false;
}

/*******************************************************************\

Function: dereferencet::build_reference_to

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dereferencet::build_reference_to(
  const exprt &what,
  const modet mode,
  const exprt &pointer_expr,
  const guardt &guard,
  exprt &value,
  exprt &pointer_guard)
{
  const typet &dereference_type=
    ns.follow(pointer_expr.type()).subtype();

  value.make_nil();
  pointer_guard.make_false();
  
  if(what.id()==ID_unknown ||
     what.id()==ID_invalid)
  {
    if(options.get_bool_option("pointer-check"))
    {
      // constraint that it actually is an invalid pointer

      exprt invalid_pointer_expr("invalid-pointer", bool_typet());
      invalid_pointer_expr.copy_to_operands(pointer_expr);
      
      // produce new guard
      
      guardt tmp_guard(guard);
      tmp_guard.add(invalid_pointer_expr);
      dereference_callback.dereference_failure(
        "pointer dereference",
        "invalid pointer", 
        tmp_guard);
    }
    
    return;
  }
  
  if(what.id()!=ID_object_descriptor)
    throw "unknown points-to: "+what.id_string();
  
  const object_descriptor_exprt &o=to_object_descriptor_expr(what);

  const exprt &root_object=o.root_object();
  const exprt &object=o.object();
  
  if(root_object.id()=="NULL-object")
  {
    if(options.get_bool_option("pointer-check"))
    {
      null_pointer_exprt null_pointer(to_pointer_type(pointer_expr.type()));

      guardt tmp_guard(guard);
      
      if(o.offset().is_zero())
      {
        tmp_guard.add(equality_exprt(pointer_expr, null_pointer));

        dereference_callback.dereference_failure(
          "pointer dereference",
          "NULL pointer", tmp_guard);
      }
      else
      {
        exprt pointer_guard(ID_same_object, bool_typet());
        pointer_guard.copy_to_operands(pointer_expr, null_pointer);
        tmp_guard.add(pointer_guard);

        dereference_callback.dereference_failure(
          "pointer dereference",
          "NULL plus offset pointer", tmp_guard);
      }
    }
  }
  else if(root_object.id()==ID_dynamic_object)
  {
    //const dynamic_object_exprt &dynamic_object=
    //  to_dynamic_object_expr(root_object);
    
    // can't remove here
  
    value=exprt(ID_dereference, dereference_type);
    value.copy_to_operands(pointer_expr);

    if(options.get_bool_option("pointer-check"))
    {
      // constraint that it actually is a dynamic object

      exprt dynamic_object_expr(ID_dynamic_object, bool_typet());
      dynamic_object_expr.copy_to_operands(pointer_expr);

      //if(!dynamic_object.valid().is_true())
      {
        // check if it is still alive
        guardt tmp_guard(guard);
        tmp_guard.add(dynamic_object_expr);
        tmp_guard.add(gen_not(valid_object(ns, pointer_expr)));
        dereference_callback.dereference_failure(
          "pointer dereference",
          "invalidated dynamic object", 
          tmp_guard);
      }

      if(options.get_bool_option("bounds-check"))
      {
        if(!o.offset().is_zero())
        {
          // check lower bound
          exprt zero=gen_zero(index_type());
          assert(zero.is_not_nil());

          exprt object_offset=unary_exprt(
            ID_pointer_offset, pointer_expr, index_type());

          binary_relation_exprt
            inequality(object_offset, ID_lt, zero);

          guardt tmp_guard(guard);
          tmp_guard.add(dynamic_object_expr);
          tmp_guard.add(inequality);
          dereference_callback.dereference_failure(
            "pointer dereference",
            "dynamic object lower bound", tmp_guard);
        }

        {
          // check upper bound
          exprt size_expr=dynamic_size(ns, pointer_expr);
            
          mp_integer element_size=
            pointer_offset_size(ns, dereference_type);
          
          if(element_size!=1)
          {
            exprt element_size_expr=
              from_integer(element_size, size_type());
          
            size_expr=binary_exprt(
              size_expr, ID_mult, element_size_expr, size_type());
          }

          exprt object_offset=
            unary_exprt(ID_pointer_offset, pointer_expr, index_type());
          object_offset.make_typecast(size_type());

          binary_relation_exprt
            inequality(size_expr, ID_le, object_offset);

          guardt tmp_guard(guard);
          tmp_guard.add(dynamic_object_expr);
          tmp_guard.add(inequality);
          dereference_callback.dereference_failure(
            "pointer dereference",
            "dynamic object upper bound", tmp_guard);
        }
      }
    }
  }
  else if(root_object.id()==ID_integer_address)
  {
    // this is stuff like *((char *)5)
    const symbolt &memory_symbol=ns.lookup(CPROVER_PREFIX "memory");
    
    exprt symbol_expr=symbol_exprt(memory_symbol.name, memory_symbol.type);

    exprt pointer_offset=unary_exprt(
      ID_pointer_offset, pointer_expr, index_type());
    
    exprt index_expr=index_exprt(symbol_expr, pointer_offset);
    index_expr.type()=ns.follow(memory_symbol.type).subtype();

    if(base_type_eq(index_expr.type(), dereference_type, ns))
    {
      // types match already, what a coincidence!
    }
    else
    {
      // not quite ok
      value=typecast_exprt(index_expr, dereference_type);
    }
  }
  else
  {
    address_of_exprt object_pointer(object);

    if(o.offset().is_zero())
    {
      equality_exprt equality(pointer_expr, object_pointer);

      if(ns.follow(equality.lhs().type())!=ns.follow(equality.rhs().type()))
        equality.lhs().make_typecast(equality.rhs().type());

      pointer_guard=equality;
    }
    else
    {
      pointer_guard=exprt(ID_same_object, bool_typet());
      pointer_guard.copy_to_operands(pointer_expr, object_pointer);
    }

    guardt tmp_guard(guard);
    tmp_guard.add(pointer_guard);
    
    valid_check(object, tmp_guard, mode);
    
    const typet &object_type=ns.follow(object.type());
    const exprt &root_object=o.root_object();
    const typet &root_object_type=ns.follow(root_object.type());
    
    if(dereference_type_compare(object_type, dereference_type) && 
       o.offset().is_zero())
    {
      // The simplest case: types match, and offset is zero!
      // This is great, we are almost done.

      value=object;

      if(object_type!=ns.follow(dereference_type))
        value.make_typecast(dereference_type);
    }
    else if(root_object_type.id()==ID_array &&
            dereference_type_compare(root_object_type.subtype(), dereference_type))
    {
      // we have an array with a subtype that matches
      // the dereferencing type
      // we will require well-alignedness!
      
      exprt offset;

      // this should work as the object is essentially the root object    
      if(o.offset().is_constant())
        offset=o.offset();
      else
        offset=unary_exprt(ID_pointer_offset, pointer_expr, index_type());

      exprt adjusted_offset;
      
      // are we doing a byte?
      mp_integer element_size=
        pointer_offset_size(ns, dereference_type);
          
      if(element_size==1)
      {
        // no need to adjust offset
        adjusted_offset=offset;
      }
      else
      {
        exprt element_size_expr=
          from_integer(element_size, offset.type());
          
        adjusted_offset=binary_exprt(
          offset, ID_div, element_size_expr, offset.type());
          
        // TODO: need to assert well-alignedness
      }
      
      index_exprt index_expr=
        index_exprt(root_object, adjusted_offset, root_object_type.subtype());

      bounds_check(index_expr, guard);
      
      value=index_expr;

      if(ns.follow(value.type())!=ns.follow(dereference_type))
        value.make_typecast(dereference_type);
    }
    else
    {
      // we extract something from the root object
      value=o.root_object();

      // this is relative to the root object
      const exprt offset=
        unary_exprt(ID_pointer_offset, pointer_expr, index_type());
    
      if(memory_model(value, dereference_type, tmp_guard, offset))
      {
        // ok, done
      }
      else
      {
        if(options.get_bool_option("pointer-check"))
        {
          std::string msg="memory model not applicable (got `";
          msg+=from_type(ns, "", value.type());
          msg+="', expected `";
          msg+=from_type(ns, "", dereference_type);
          msg+="')";

          dereference_callback.dereference_failure(
            "pointer dereference",
            msg, tmp_guard);
        }

        value.make_nil();
        return; // give up, no way that this is ok
      }
    }
  }
}

/*******************************************************************\

Function: dereferencet::valid_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dereferencet::valid_check(
  const exprt &object,
  const guardt &guard,
  const modet mode)
{
  if(!options.get_bool_option("pointer-check"))
    return;

  const exprt &symbol_expr=get_symbol(object);

  if(symbol_expr.id()==ID_string_constant)
  {
    // always valid, but can't write
    
    if(mode==WRITE)
    {
      dereference_callback.dereference_failure(
        "pointer dereference",
        "write access to string constant",
        guard);
    }
  }
  else if(symbol_expr.is_nil() ||
          symbol_expr.get_bool("#invalid_object"))
  { 
    // always "valid", shut up
    return;
  }
  else if(symbol_expr.id()==ID_symbol)
  {
    const irep_idt identifier=
      to_symbol_expr(symbol_expr).get_identifier();
    
    const symbolt &symbol=ns.lookup(identifier);
    
    if(symbol.type.get_bool(ID_C_is_failed_symbol))
    {
      dereference_callback.dereference_failure(
        "pointer dereference",
        "invalid pointer",
        guard);
    }

    #if 0  
    if(dereference_callback.is_valid_object(identifier))
      return; // always ok
    #endif
  }
}

/*******************************************************************\

Function: dereferencet::bounds_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dereferencet::bounds_check(
  const index_exprt &expr,
  const guardt &guard)
{
  if(!options.get_bool_option("pointer-check"))
    return;

  if(!options.get_bool_option("bounds-check"))
    return;

  const typet &array_type=ns.follow(expr.op0().type());

  if(array_type.id()!=ID_array)
    throw "bounds check expected array type";

  std::string name=array_name(ns, expr.array());
  
  {
    mp_integer i;
    if(!to_integer(expr.index(), i) &&
       i>=0)
    {
    }
    else
    {
      exprt zero=gen_zero(expr.index().type());

      if(zero.is_nil())
        throw "no zero constant of index type "+
          expr.index().type().to_string();

      binary_relation_exprt
        inequality(expr.index(), ID_lt, zero);

      guardt tmp_guard(guard);
      tmp_guard.add(inequality);
      dereference_callback.dereference_failure(
        "array bounds",
        name+" lower bound", tmp_guard);
    }
  }

  const exprt &size_expr=
    to_array_type(array_type).size();

  if(size_expr.id()!=ID_infinity)
  {
    if(size_expr.is_nil())
      throw "index array operand of wrong type";

    binary_relation_exprt inequality(expr.index(), ID_ge, size_expr);

    if(c_implicit_typecast(
      inequality.op0(),
      inequality.op1().type(),
      ns))
      throw "index address of wrong type";

    guardt tmp_guard(guard);
    tmp_guard.add(inequality);
    dereference_callback.dereference_failure(
      "array bounds",
      name+" upper bound", tmp_guard);
  }
}

/*******************************************************************\

Function: dereferencet::memory_model

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static unsigned bv_width(const typet &type)
{
  return atoi(type.get(ID_width).c_str());
}

static bool is_a_bv_type(const typet &type)
{
  return type.id()==ID_unsignedbv ||
         type.id()==ID_signedbv ||
         type.id()==ID_bv ||
         type.id()==ID_fixedbv ||
         type.id()==ID_floatbv;
}

bool dereferencet::memory_model(
  exprt &value,
  const typet &to_type,
  const guardt &guard,
  const exprt &offset)
{
  // we will allow more or less arbitrary pointer type cast

  const typet from_type=value.type();

  // first, check if it's really just a conversion,
  // i.e., both are bit-vector types and the size is
  // exacly the same

  if(is_a_bv_type(from_type) &&
     is_a_bv_type(to_type) &&
     bv_width(from_type)==bv_width(to_type))
    return memory_model_conversion(value, to_type, guard, offset);

  // otherwise, we will stich it together from bytes
  
  return memory_model_bytes(value, to_type, guard, offset);
}

/*******************************************************************\

Function: dereferencet::memory_model_conversion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool dereferencet::memory_model_conversion(
  exprt &value,
  const typet &to_type,
  const guardt &guard,
  const exprt &offset)
{
  const typet from_type=value.type();

  // avoid semantic conversion in case of
  // cast to float or fixed-point
  if(from_type.id()!=ID_bv &&
     (to_type.id()==ID_fixedbv || to_type.id()==ID_floatbv))
  {
    value.make_typecast(bv_typet(bv_width(from_type)));
    value.make_typecast(to_type);
  }
  else
  {
    // only doing type conversion
    // just do the typecast
    value.make_typecast(to_type);
  }

  // also assert that offset is zero

  if(options.get_bool_option("pointer-check"))
  {
    equality_exprt offset_not_zero(offset, gen_zero(offset.type()));
    offset_not_zero.make_not();
  
    guardt tmp_guard(guard);
    tmp_guard.add(offset_not_zero);
    dereference_callback.dereference_failure(
      "word bounds",
      "offset not zero", tmp_guard);
  }

  return true;
}

/*******************************************************************\

Function: dereferencet::memory_model_bytes

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool dereferencet::memory_model_bytes(
  exprt &value,
  const typet &to_type,
  const guardt &guard,
  const exprt &offset)
{
  const typet from_type=value.type();
  
  // we refuse to convert to/from code
  if(from_type.id()==ID_code || to_type.id()==ID_code)
    return false;

  // won't do this without a committment to an endianess
  if(config.ansi_c.endianess==configt::ansi_ct::NO_ENDIANESS)
    return false; 

  // But anything else we will try!

  // We allow reading more or less _anything_ (but code)
  // as a bit-vector.
  if(to_type.id()==ID_bv ||
     to_type.id()==ID_unsignedbv ||
     to_type.id()==ID_signedbv)
  {
    exprt byte_extract(byte_extract_id(), to_type);
    byte_extract.copy_to_operands(value, offset);
    value=byte_extract;
  
    // are we within the bounds?
    if(options.get_bool_option("pointer-check"))
    {
      // upper bound
      {
        mp_integer from_width=pointer_offset_size(ns, from_type);
        mp_integer to_width=pointer_offset_size(ns, to_type);
      
        exprt bound=from_integer(from_width-to_width, offset.type());

        binary_relation_exprt
          offset_upper_bound(offset, ID_gt, bound);
        
        guardt tmp_guard(guard);
        tmp_guard.add(offset_upper_bound);
        dereference_callback.dereference_failure(
          "pointer dereference",
          "object upper bound", tmp_guard);
      }

      // lower bound is easy
      if(!offset.is_zero())
      {
        binary_relation_exprt
          offset_lower_bound(offset, ID_lt,
                             gen_zero(offset.type()));

        guardt tmp_guard(guard);
        tmp_guard.add(offset_lower_bound);                
        dereference_callback.dereference_failure(
          "pointer dereference",
          "object lower bound", tmp_guard);
      }
    }

    return true;
  }
  
  return false;
}

/*******************************************************************\

Function: dereferencet::byte_extract_id

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt dereferencet::byte_extract_id()
{
  switch(config.ansi_c.endianess)
  {
  case configt::ansi_ct::IS_LITTLE_ENDIAN:
    return ID_byte_extract_little_endian;

  case configt::ansi_ct::IS_BIG_ENDIAN:
    return ID_byte_extract_big_endian;
    
  default:
    assert(false);
  }
}
