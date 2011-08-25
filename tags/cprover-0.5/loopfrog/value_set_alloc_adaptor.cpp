/*******************************************************************\

 Module: Adaptor for value sets (dynamic object removal)

 Author: CM Wintersteiger

\*******************************************************************/

#include <std_expr.h>
#include <std_types.h>
#include <arith_tools.h>
#include <i2string.h>
#include <prefix.h>
#include <ansi-c/c_types.h>

#include "value_set_alloc_adaptor.h"

static std::string ad_prefix = "alloc_adaptor::";

/*******************************************************************\

Function: value_set_alloc_adaptort::get_values

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_alloc_adaptort::get_values(
  goto_programt::const_targett l,
  const exprt &expr,
  valuest &dest)
{
  value_sets.get_values(l, expr, dest);

  for(valuest::iterator it=dest.begin();
      it!=dest.end();
      it++)
  {
    replace_dynamic_objects(*it);
  }

  #if 0
  std::cout << "ALLOC_ADAPTOR::GET_VALUE_SET" << std::endl;
  for(valuest::const_iterator it=dest.begin();
      it!=dest.end();
      it++)
    std::cout << "E:" << *it << std::endl;
  #endif
}

/*******************************************************************\

Function: value_set_alloc_adaptort::get_values

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_alloc_adaptort::replace_dynamic_objects(exprt &expr)
{
  if(expr.id()=="object_descriptor")
  {
    object_descriptor_exprt &obj=to_object_descriptor_expr(expr);

    // get root object
    exprt *root_obj=&obj.object();

    while(root_obj->id()=="member" ||
          root_obj->id()=="index" ||
          root_obj->id()=="typecast")
    {
      assert(root_obj->operands().size()!=0);
      root_obj=&root_obj->op0();
    }

    if(root_obj->id()=="dynamic_object")
    {
      const dynamic_object_exprt &dynobj=to_dynamic_object_expr(*root_obj);
      const exprt &instance=dynobj.instance();

      mp_integer i_nr;
      to_integer(instance, i_nr);

      std::string new_name = std::string("static_object$") +
                               integer2string(i_nr);

      typet type("array");

      contextt::symbolst::const_iterator s_it =
        context.symbols.find(ad_prefix+new_name);

      if(s_it!=context.symbols.end())
      {
        // we're not replacing malloc, this is for real.
        type = s_it->second.type;
      }
      else
      {
        type.subtype()=dynobj.type();
        // no size!
      }

      index_exprt inx;
      inx.array() = symbol_exprt(ad_prefix+new_name, type);
      
      if(obj.offset().is_nil())
        inx.index() = obj.offset();
      else
        inx.index() = gen_zero(index_type());
      
      inx.type() = type.subtype();

      root_obj->swap(inx);
    }
  }
}

/*******************************************************************\

Function: value_set_alloc_adaptort::get_values

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

//void value_set_alloc_adaptort::get_values(
//  goto_programt::const_targett l,
//  value_set_valuest &dest)
//{
//  value_set_valuest temp;
//  value_sets.get_values(l, temp);
//
////  for(value_set_valuest::iterator it=temp.begin();
////      it!=temp.end();
////      it++)
////  {
////    for(value_set_object_map_dt::const_iterator oit =
////          it->second.object_map.read().begin();
////        oit!=it->second.object_map.read().end();
////        oit++)
////    {
////      replace_dynamic_objects(*it);
////    }
////  }
//}
