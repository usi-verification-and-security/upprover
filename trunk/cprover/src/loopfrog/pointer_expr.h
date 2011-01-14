/*******************************************************************

 Module: Pointer Expressions

 Author: CM Wintersteiger

 \*******************************************************************/

#ifndef CPROVER_LOOPFROG_POINTER_EXPR_H_
#define CPROVER_LOOPFROG_POINTER_EXPR_H_

#include <expr.h>
#include <std_expr.h>
#include <ansi-c/c_types.h>
#include <std_types.h>
#include <config.h>
#include <util/mp_arith.h>


class pointer_offset_exprt : public exprt
{
public:
  pointer_offset_exprt(const exprt &ptr) :
    exprt(ID_pointer_offset, index_type())
  {
    copy_to_operands(ptr);
  }
};

class invalid_pointer_exprt : public exprt
{
public:
  invalid_pointer_exprt(const exprt &obj) :
    exprt("valid_object", bool_typet())
  {
    copy_to_operands(obj);
    make_not();
  }
};

class valid_pointer_exprt : public exprt
{
public:
  valid_pointer_exprt(const exprt &obj) :
    exprt("valid_object", bool_typet())
  {
    copy_to_operands(obj);
  }
};

class non_null_pointer_exprt : public exprt
{
public:
  non_null_pointer_exprt(const exprt &obj) :
    exprt(ID_not, bool_typet())
  {    
    exprt pointer(ID_constant, typet(ID_pointer));
    pointer.type().subtype()=obj.type();
    pointer.set(ID_value, ID_NULL);

    exprt n("same-object", bool_typet());
    n.reserve_operands(2);
    n.copy_to_operands(obj);
    n.move_to_operands(pointer);
        
    move_to_operands(n);
  }
};

class dynamic_object_pointer_exprt : public exprt
{
public:
  dynamic_object_pointer_exprt(const exprt &obj) :
    exprt("is_dynamic_object", bool_typet())
  {
    copy_to_operands(obj);
  }
};

class static_object_pointer_exprt : public exprt
{
public:
  static_object_pointer_exprt(const exprt &ptr, const exprt &obj) :
    exprt("same-object", bool_typet())
  {
    address_of_exprt a(obj);
    copy_to_operands(ptr);
    move_to_operands(a);
  }
};

class pointer_offset_equals_exprt : public equality_exprt
{
public:
  pointer_offset_equals_exprt(const exprt &obj, const exprt &offset) :
    equality_exprt(pointer_offset_exprt(obj), offset)
  {
  }
};

class nondet_exprt : public exprt
{
public:
  nondet_exprt(const typet &type) :
    exprt(ID_sideeffect, type)
  {
    set(ID_statement, ID_nondet);
  }
};

class zero_string_exprt : public symbol_exprt
{
public:
  zero_string_exprt(const exprt &str) :
    symbol_exprt()
  {
    type() = bool_typet();
    set_identifier(id2string(str.get(ID_identifier))+"#is_zero_string");
  }
};

class string_length_exprt : public symbol_exprt
{
public:
  string_length_exprt(const exprt &str) :
    symbol_exprt()
  {
    type() = uint_type();
    set_identifier(id2string(str.get(ID_identifier))+"#length");
  }
};

class integer_exprt : public exprt
{
public:
  integer_exprt(const int &val, const typet &type) :
    exprt(ID_constant, type)
  {
    set(ID_value, integer2binary(val, config.ansi_c.int_width));
  }
};

class same_object_exprt : public exprt
{
public:
  same_object_exprt(const exprt &obj1,const exprt &obj2) :
    exprt("same-object", bool_typet())
  {
    copy_to_operands(obj1,obj2);
  }
};

#endif /*CPROVER_LOOPFROG_POINTER_EXPR_H_*/
