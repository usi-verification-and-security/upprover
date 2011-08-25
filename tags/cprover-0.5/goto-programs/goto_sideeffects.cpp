/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <expr_util.h>
#include <std_expr.h>
#include <rename.h>
#include <cprover_prefix.h>
#include <i2string.h>

#include <ansi-c/c_types.h>

#include "goto_convert_class.h"

/*******************************************************************\

Function: goto_convertt::has_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool goto_convertt::has_function_call(const exprt &expr)
{
  forall_operands(it, expr)
    if(has_function_call(*it))
      return true;

  if(expr.id()==ID_sideeffect &&
     expr.get(ID_statement)==ID_function_call)
    return true;

  return false;
}

/*******************************************************************\

Function: goto_convertt::remove_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::remove_assignment(
  side_effect_exprt &expr,
  goto_programt &dest)
{
  codet assignment_statement(ID_expression);
  assignment_statement.copy_to_operands(expr);
  assignment_statement.location()=expr.location();

  if(expr.operands().size()!=2)
    throw "assignment must have two operands";

  exprt lhs;
  lhs.swap(expr.op0());
  expr.swap(lhs);

  convert(assignment_statement, dest);
}

/*******************************************************************\

Function: goto_convertt::remove_pre

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::remove_pre(
  side_effect_exprt &expr,
  goto_programt &dest)
{
  codet pre_statement(ID_expression);
  pre_statement.copy_to_operands(expr);

  if(expr.operands().size()!=1)
    throw "preincrement/predecrement must have one operand";

  exprt op;
  op.swap(expr.op0());
  expr.swap(op);

  convert(pre_statement, dest);
}

/*******************************************************************\

Function: goto_convertt::remove_post

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::remove_post(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  // we have ...(op++)...
  codet post_statement(ID_expression);
  post_statement.copy_to_operands(expr);

  if(expr.operands().size()!=1)
    throw "postincrement/postdecrement must have one operand";

  if(result_is_used)
  {
    exprt tmp;
    tmp.swap(expr.op0());
    make_temp_symbol(tmp, "post", dest);
    expr.swap(tmp);
  }
  else
  {
    expr.make_nil();
  }

  convert(post_statement, dest);
}

/*******************************************************************\

Function: goto_convertt::remove_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::remove_function_call(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  if(!result_is_used)
  {
    code_expressiont call;
    call.expression()=expr;
    convert(call, dest);
    return;
  }

  symbolt new_symbol;

  new_symbol.base_name="return_value";
  new_symbol.lvalue=true;
  new_symbol.is_statevar=true;
  new_symbol.thread_local=true;
  new_symbol.type=expr.type();
  new_symbol.location=expr.find_location();

  // get name of function, if available

  if(expr.id()!=ID_sideeffect ||
     expr.get(ID_statement)!=ID_function_call)
    throw "expected function call";

  if(expr.operands().empty())
    throw "function_call expects at least one operand";

  if(expr.op0().id()==ID_symbol)
  {
    const irep_idt &identifier=expr.op0().get(ID_identifier);
    const symbolt &symbol=lookup(identifier);
    
    std::string new_base_name=id2string(new_symbol.base_name);
    
    new_base_name+="_";
    new_base_name+=id2string(symbol.base_name);
    new_base_name+="$"+i2string(++temporary_counter);
    
    new_symbol.base_name=new_base_name;
    new_symbol.mode=symbol.mode;
  }

  new_symbol.name=tmp_symbol_prefix+id2string(new_symbol.base_name);

  new_name(new_symbol);
  
  tmp_symbols.push_back(new_symbol.name);
  
  {
    code_declt decl;
    decl.symbol()=symbol_expr(new_symbol);
    decl.location()=new_symbol.location;
    convert(decl, dest);
  }

  {
    goto_programt tmp_program2;
    code_assignt assignment(symbol_expr(new_symbol), expr);
    assignment.location()=new_symbol.location;
    convert(assignment, dest);
  }

  static_cast<exprt &>(expr)=symbol_expr(new_symbol);
}

/*******************************************************************\

Function: goto_convertt::replace_new_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::replace_new_object(
  const exprt &object,
  exprt &dest)
{
  if(dest.id()=="new_object")
    dest=object;
  else
    Forall_operands(it, dest)
      replace_new_object(object, *it);
}

/*******************************************************************\

Function: goto_convertt::remove_cpp_new

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::remove_cpp_new(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  codet call;

  if(result_is_used)
  {
    symbolt new_symbol;

    new_symbol.base_name="new_value$"+i2string(++temporary_counter);
    new_symbol.lvalue=true;
    new_symbol.type=expr.type();
    new_symbol.name=tmp_symbol_prefix+id2string(new_symbol.base_name);

    new_name(new_symbol);
    tmp_symbols.push_back(new_symbol.name);

    call=code_assignt(symbol_expr(new_symbol), expr);

    static_cast<exprt &>(expr)=symbol_expr(new_symbol);
  }
  else
  {
    call=codet(ID_expression);
    call.move_to_operands(expr);
  }

  convert(call, dest);
}

/*******************************************************************\

Function: goto_convertt::remove_malloc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::remove_malloc(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  codet call;

  if(result_is_used)
  {
    symbolt new_symbol;

    new_symbol.base_name="new_value$"+i2string(++temporary_counter);
    new_symbol.lvalue=true;
    new_symbol.type=expr.type();
    new_symbol.name=tmp_symbol_prefix+id2string(new_symbol.base_name);

    new_name(new_symbol);
    tmp_symbols.push_back(new_symbol.name);

    call=code_assignt(symbol_expr(new_symbol), expr);
    
    static_cast<exprt &>(expr)=symbol_expr(new_symbol);
  }
  else
  {
    call=codet(ID_expression);
    call.move_to_operands(expr);
  }

  convert(call, dest);
}

/*******************************************************************\

Function: goto_convertt::remove_temporary_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::remove_temporary_object(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  if(expr.operands().size()!=1 &&
     expr.operands().size()!=0)
    throw "temporary_object takes 0 or 1 operands";

  symbolt &new_symbol=
    new_tmp_symbol(expr.type(), "obj", dest, expr.find_location());

  new_symbol.mode=expr.get(ID_mode);
  
  if(expr.operands().size()==1)
  {
    codet assignment(ID_assign);
    assignment.reserve_operands(2);
    assignment.copy_to_operands(symbol_expr(new_symbol));
    assignment.move_to_operands(expr.op0());

    convert(assignment, dest);
  }

  if(expr.find(ID_initializer).is_not_nil())
  {
    assert(expr.operands().empty());
    exprt initializer=static_cast<const exprt &>(expr.find(ID_initializer));
    replace_new_object(symbol_expr(new_symbol), initializer);

    convert(to_code(initializer), dest);
  }

  static_cast<exprt &>(expr)=symbol_expr(new_symbol);  
}

/*******************************************************************\

Function: goto_convertt::remove_statement_expression

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::remove_statement_expression(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  if(expr.operands().size()!=1)
    throw "statement_expression takes 1 operand";

  if(expr.op0().id()!=ID_code)
    throw "statement_expression takes code as operand";

  codet &code=to_code(expr.op0());

  if(!result_is_used)
  {
    convert(code, dest);
    return;
  }
  
  // get last statement from block
  codet *last=&code;
    
  while(true)
  {
    if(last->get_statement()==ID_block)
    {
      if(last->operands().empty())
        throw "statement_expression expects non-empty block";
      
      last=&to_code(last->operands().back());
    }
    else if(last->get_statement()==ID_label)
    {
      assert(last->operands().size()==1);
      last=&to_code(last->op0());
    }
    else
      break;
  }

  codet old_last=*last;
  last->set_statement(ID_skip);
  
  convert(code, dest);

  {
    clean_expr(old_last, dest, true);

    if(old_last.get(ID_statement)==ID_expression &&
       old_last.operands().size()==1)
      static_cast<exprt &>(expr)=old_last.op0();
    else
      throw "statement_expression expects expression as "
            "last statement, but got `"+
            id2string(old_last.get(ID_statement))+"'";
  }
}

/*******************************************************************\

Function: goto_convertt::remove_side_effect

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::remove_side_effect(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  const irep_idt &statement=expr.get(ID_statement);

  if(statement==ID_function_call)
    remove_function_call(expr, dest, result_is_used);
  else if(statement==ID_assign ||
          statement==ID_assign_plus ||
          statement==ID_assign_minus ||
          statement==ID_assign_mult ||
          statement==ID_assign_div ||
          statement==ID_assign_bitor ||
          statement==ID_assign_bitxor ||
          statement==ID_assign_bitand ||
          statement==ID_assign_lshr ||
          statement==ID_assign_ashr ||
          statement==ID_assign_shl ||
          statement==ID_assign_mod)
    remove_assignment(expr, dest);
  else if(statement==ID_postincrement ||
          statement==ID_postdecrement)
    remove_post(expr, dest, result_is_used);
  else if(statement==ID_preincrement ||
          statement==ID_predecrement)
    remove_pre(expr, dest);
  else if(statement==ID_cpp_new ||
          statement=="cpp_new[]")
    remove_cpp_new(expr, dest, result_is_used);
  else if(statement==ID_malloc)
    remove_malloc(expr, dest, result_is_used);
  else if(statement=="temporary_object")
    remove_temporary_object(expr, dest, result_is_used);
  else if(statement==ID_statement_expression)
    remove_statement_expression(expr, dest, result_is_used);
  else if(statement==ID_nondet)
  {
    // these are fine
  }
  else
  {
    str << "cannot remove side effect (" << statement << ")";
    throw 0;
  }
}

