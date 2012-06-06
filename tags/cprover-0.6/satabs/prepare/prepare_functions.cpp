/*******************************************************************\
  
Module: Prepare a C program for use by CEGAR

Author: Daniel Kroening

Date:   September 2009
 
\*******************************************************************/

#include <std_code.h>
#include <std_expr.h>

#include "prepare_functions.h"

class prepare_functionst:public messaget
{
public:
  prepare_functionst(contextt &_context):context(_context)
  {
  }

  void operator()(
    goto_functionst &goto_functions);

protected:
  typedef std::map<irep_idt, code_typet> original_typest;
  original_typest original_types;
  
  contextt &context;

  void adjust_function_arguments(
    const code_typet::argumentst &arguments);

  void do_return_value(
    goto_functionst::function_mapt::iterator f_it);

  void do_function_calls(
    goto_functionst &goto_functions,
    goto_programt &goto_program);

  void do_function_arguments(
    goto_functionst::function_mapt::iterator f_it);

  std::set<irep_idt> no_body_set;
};

/*******************************************************************\

Function: prepare_functionst::adjust_function_arguments

  Inputs:

 Outputs:

 Purpose: turns function arguments into thread-local variables

\*******************************************************************/

void prepare_functionst::adjust_function_arguments(
  const code_typet::argumentst &arguments)
{
  for(code_typet::argumentst::const_iterator
      a_it=arguments.begin();
      a_it!=arguments.end();
      a_it++)
  {
    const irep_idt &identifier=a_it->get_identifier();
    
    if(identifier=="") continue;
    
    const contextt::symbolst::iterator s_it=
      context.symbols.find(identifier);
    
    assert(s_it!=context.symbols.end());
    
    symbolt &symbol=s_it->second;
    
    symbol.thread_local=true;
    symbol.file_local=false;
    symbol.static_lifetime=true;
  } 
}

/*******************************************************************\

Function: prepare_functionst::do_return_value

  Inputs:

 Outputs:

 Purpose: turns 'return x' into an assignment and 'return'

\*******************************************************************/

void prepare_functionst::do_return_value(
  goto_functionst::function_mapt::iterator f_it)
{
  typet return_type=f_it->second.type.return_type();

  // returns void?
  if(return_type==empty_typet())
    return;

  // look up the function symbol
  const irep_idt function_id=f_it->first;

  contextt::symbolst::iterator s_it=
    context.symbols.find(function_id);

  assert(s_it!=context.symbols.end());
  symbolt &function_symbol=s_it->second;
  
  // make the return type 'void'
  f_it->second.type.return_type()==empty_typet();
  function_symbol.type=f_it->second.type;

  // add symbol to context
  symbolt new_symbol;
  new_symbol.lvalue=true;
  new_symbol.is_statevar=true;
  new_symbol.thread_local=true;
  new_symbol.file_local=true;
  new_symbol.static_lifetime=true;
  new_symbol.module=function_symbol.module;
  new_symbol.value.make_nil();
  new_symbol.base_name=id2string(function_symbol.base_name)+"#return_value";
  new_symbol.name=id2string(function_symbol.name)+"#return_value";
  new_symbol.mode=function_symbol.mode;
  new_symbol.type=return_type;
  
  context.add(new_symbol);
  
  goto_programt &goto_program=f_it->second.body;

  Forall_goto_program_instructions(i_it, goto_program)
  {
    if(i_it->is_return())
    {
      assert(i_it->code.operands().size()==1);

      // replace "return x;" by "fkt#return_value=x; return;"
      symbol_exprt lhs_expr;
      lhs_expr.set_identifier(id2string(function_id)+"#return_value");
      lhs_expr.type()=return_type;
      
      code_assignt assignment(lhs_expr, i_it->code.op0());

      // now remove return value from i_it
      i_it->code.operands().resize(0);
      
      goto_programt::instructiont tmp_i;
      tmp_i.make_assignment();
      tmp_i.code=assignment;
      tmp_i.location=i_it->location;
      tmp_i.function=i_it->function;

      goto_program.insert_before_swap(i_it, tmp_i);
      
      i_it++;
    }
  }
}

/*******************************************************************\

Function: prepare_functionst::do_function_calls

  Inputs:

 Outputs:

 Purpose: turns x=f(...) into f(...); lhs=f#return_value;

\*******************************************************************/

void prepare_functionst::do_function_calls(
  goto_functionst &goto_functions,
  goto_programt &goto_program)
{
  Forall_goto_program_instructions(i_it, goto_program)
  {
    if(i_it->is_function_call())
    {
      code_function_callt &function_call=to_code_function_call(i_it->code);
    
      assert(function_call.function().id()=="symbol");

      const irep_idt function_id=
        to_symbol_expr(function_call.function()).get_identifier();
        
      // see if we have a body
      goto_functionst::function_mapt::const_iterator
        f_it=goto_functions.function_map.find(function_id);
        
      if(f_it==goto_functions.function_map.end())
        throw "failed to find function in function map";

      if(f_it->second.body_available)
      {
        // replace "lhs=f(...)" by "f(...); lhs=f#return_value;"
        code_typet old_type=to_code_type(function_call.function().type());

        if(old_type.return_type()!=empty_typet())
        {
          // fix the type
          to_code_type(function_call.function().type()).return_type()=empty_typet();
  
          if(function_call.lhs().is_not_nil())
          {
            symbol_exprt rhs;
            rhs.type()=function_call.lhs().type();
            rhs.set_identifier(id2string(function_id)+"#return_value");

            goto_programt::targett t=goto_program.insert_after(i_it);
            t->make_assignment();
            t->location=i_it->location;
            t->code=code_assignt(function_call.lhs(), rhs);
            t->function=i_it->function;

            // fry the previous assignment
            function_call.lhs().make_nil();
          }
        }
      }
      else // no body available
      {
        if(no_body_set.insert(f_it->first).second)
          warning("no body for function `"+id2string(f_it->first)+"'");
      
        goto_programt tmp;

        // evaluate function arguments -- they might have
        // pointer dereferencing or the like
        const exprt::operandst &arguments=function_call.arguments();
        forall_expr(a_it, arguments)
        {
          goto_programt::targett t=tmp.add_instruction();
          t->make_other();
          t->location=i_it->location;
          t->function=i_it->function;
          t->code=codet("expression");
          t->code.copy_to_operands(*a_it);
        }
        
        // return value
        if(function_call.lhs().is_not_nil())
        {
          exprt rhs=exprt("sideeffect", function_call.lhs().type());
          rhs.set("statement", "nondet");
          rhs.location()=i_it->location;

          code_assignt code(function_call.lhs(), rhs);
          code.location()=i_it->location;
        
          goto_programt::targett t=tmp.add_instruction(ASSIGN);
          t->location=i_it->location;
          t->function=i_it->function;
          t->code.swap(code);
        }

        // now just kill call
        i_it->type=LOCATION;
        i_it->code.clear();        

        // insert tmp
        goto_programt::targett next=i_it; next++;
        goto_program.destructive_insert(next, tmp);
      }
    }
  }
}

/*******************************************************************\

Function: prepare_functionst::do_function_arguments

  Inputs:

 Outputs:

 Purpose: replace function arguments by assignments to
          thread-local variables

\*******************************************************************/

void prepare_functionst::do_function_arguments(
  goto_functionst::function_mapt::iterator f_it)
{
  {
    // look up the function symbol
    const irep_idt function_id=f_it->first;

    contextt::symbolst::iterator s_it=
      context.symbols.find(function_id);

    assert(s_it!=context.symbols.end());
    symbolt &function_symbol=s_it->second;

    // adjust type of function
    f_it->second.type.arguments().clear();
    function_symbol.type=f_it->second.type;
  }  

  const irep_idt function_id=f_it->first;
  goto_programt &goto_program=f_it->second.body;

  Forall_goto_program_instructions(i_it, goto_program)
  {
    if(!i_it->is_function_call()) continue;
    
    code_function_callt old_function_call=to_code_function_call(i_it->code);
    assert(old_function_call.function().id()=="symbol");
    irep_idt identifier=
      to_symbol_expr(old_function_call.function()).get_identifier();
    const code_typet &old_type=original_types[identifier];
    
    // replace f(a, b, c) by "x1=a; x2=b; x3=c; f();"
    // this doesn't really work in case of recursive calls
    
    // first clean up and adjust type
    code_function_callt &function_call=to_code_function_call(i_it->code);
    function_call.arguments().resize(0);
    to_code_type(function_call.function().type()).arguments().clear();    
    
    for(unsigned i=0; i<old_function_call.arguments().size(); i++)
    {
      if(i>=old_type.arguments().size()) break;
      const code_typet::argumentt &a=old_type.arguments()[i];
      exprt value=old_function_call.arguments()[i];
      const irep_idt &argument_identifier=a.get_identifier();

      if(argument_identifier!="")
      {
        symbol_exprt lhs;
        lhs.type()=a.type();
        lhs.set_identifier(argument_identifier);
        
        if(lhs.type()!=value.type())
          value.make_typecast(lhs.type());

        goto_programt::instructiont tmp_i;
        tmp_i.make_assignment();
        tmp_i.location=i_it->location;
        tmp_i.code=code_assignt(lhs, value);
        tmp_i.function=i_it->function;

        goto_program.insert_before_swap(i_it, tmp_i);
        i_it++;
      }
    }
    
  }
}

/*******************************************************************\

Function: prepare_functionst::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void prepare_functionst::operator()(goto_functionst &goto_functions)
{
  // first collect the original types

  forall_goto_functions(it, goto_functions)
    original_types[it->first]=it->second.type;

  // now modify stuff

  Forall_goto_functions(it, goto_functions)
  {
    if(it->second.body_available)
      adjust_function_arguments(original_types[it->first].arguments());
    do_return_value(it);
    do_function_calls(goto_functions, it->second.body);
    do_function_arguments(it);
  }
}

/*******************************************************************\

Function: prepare_functions

  Inputs:

 Outputs:

 Purpose: convert input program into goto program

\*******************************************************************/

void prepare_functions(
  contextt &context,
  goto_functionst &goto_functions,
  message_handlert &message_handler)
{
  prepare_functionst pf(context);
  pf.set_message_handler(message_handler);
  pf(goto_functions);
}

