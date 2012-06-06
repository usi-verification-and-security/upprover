/*******************************************************************\

 Module: Dynamic object replacing

 Author: CM Wintersteiger

\*******************************************************************/

#include <prefix.h>
#include <std_expr.h>
#include <expr_util.h>
#include <ansi-c/c_types.h>

#include "pointer_expr.h"
#include "replace_malloc.h"

/*******************************************************************\

 Function: replace_malloc_at

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void replace_malloc_at(
  contextt &context,
  goto_programt &goto_program,
  const symbol_exprt &static_object,
  goto_programt::targett &next,
  const exprt &lhs,
  exprt &rhs)
{
  const irep_idt &name = static_object.get("identifier");
  const irep_idt &sizename = name.as_string() + "#size";

  std::string short_name(name.as_string(), name.as_string().find("::")+2);

  // we need new symbols for this.
  symbolt new_symbol;
  symbolt new_size_symbol;

  new_size_symbol.name=sizename;
  new_size_symbol.base_name=short_name + "#size";
  new_size_symbol.type=rhs.op0().type();

  new_symbol.name=name;
  new_symbol.base_name=short_name;
  new_symbol.lvalue=true;

  const typet &malloc_type = (typet&) rhs.find("#type");

  array_typet atype;
  atype.subtype()=malloc_type;
  atype.size()=rhs.op0();
  new_symbol.type=atype;

  // reset RHS

  typecast_exprt tc(lhs.type());

  index_exprt index;
  index.array() = symbol_exprt(new_symbol.name, new_symbol.type);
  index.index() = gen_zero(uint_type());
  index.type() = new_symbol.type.subtype();

  tc.op() = address_of_exprt(index);

  // reset the object!

  goto_programt::targett obj_nondet =
    goto_program.insert_before(next);

  obj_nondet->type=ASSIGN;
  obj_nondet->code=code_assignt(index.array(),
                                nondet_exprt(index.array().type()));

  // set size

  goto_programt::targett new_instruction =
    goto_program.insert_before(next);

  new_instruction->type=ASSIGN;
  new_instruction->code=code_assignt(
                     symbol_exprt(new_size_symbol.name, new_size_symbol.type),
                     rhs.op0());

  rhs = tc;

  context.move(new_symbol);
  context.move(new_size_symbol);
}

/*******************************************************************\

 Function: replace_malloc

 Inputs:

 Outputs:

 Purpose: Warning: This relies on alloc_adaptor being used!

\*******************************************************************/

void replace_malloc(
  contextt &context,
  goto_functionst &goto_functions,
  value_setst &value_sets)
{
  for(goto_functionst::function_mapt::iterator f_it =
        goto_functions.function_map.begin();
      f_it!=goto_functions.function_map.end();
      f_it++)
    Forall_goto_program_instructions(it, f_it->second.body)
    {
      if(it->type==ASSIGN)
      {
        code_assignt &code=to_code_assign(to_code(it->code));

        if(code.rhs().id()=="sideeffect" &&
           code.rhs().get("statement")=="malloc")
        {
          assert(code.rhs().operands().size()==1);

          // the adaptor knows the dynamic object!
          goto_programt::targett next = it; next++;

          value_setst::valuest vset;
          value_sets.get_values(it, code.rhs(), vset);

          assert(vset.size()==1); // we don't expect more than one object here

          const object_descriptor_exprt &obj=
                              to_object_descriptor_expr(vset.front());

          const exprt *root_obj=&(obj.object());

          while(root_obj->id()=="member" ||
                root_obj->id()=="index" ||
                root_obj->id()=="typecast")
          {
            assert(root_obj->operands().size()!=0);
            root_obj=&root_obj->op0();
          }

          assert(root_obj->id()=="symbol" &&
                 has_prefix(root_obj->get("identifier").as_string(),
                            "alloc_adaptor::"));

          // find the dynamic object instance
          symbol_exprt static_object=to_symbol_expr(*root_obj);


          replace_malloc_at(context,
                            f_it->second.body,
                            static_object,
                            next,
                            code.lhs(), code.rhs());

          next++->make_skip(); // dyn-obj-assumption
          next++->make_skip(); // dynsize-assumption
          next->make_skip(); // valid-bj-assumption
        }
      }
    }
}


