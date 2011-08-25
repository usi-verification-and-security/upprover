/********************************************************************\

 Module: Loop Summaries

 Author: CM Wintersteiger
         Aliaksei Tsitovich

 \*******************************************************************/

#include <std_expr.h>
#include <expr_util.h>

#include "pointer_expr.h"

#include "summary.h"

/*******************************************************************\

 Function: loop_summaryt::get_variants_program

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void loop_summaryt::get_variants_program(
  value_setst &value_sets,
  goto_programt &goto_program)
{
  for (std::set<exprt>::const_iterator i=variant.begin();
       i!=variant.end();
       i++)
  {
    assign_nondet_rec(*i, value_sets, goto_program);
  }
}

/*******************************************************************\

 Function: loop_summaryt::get_preconditions_program

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void loop_summaryt::get_preconditions_program(
  contextt &context,
  goto_programt &goto_program)
{
  unsigned counter=0;

  for (std::set<exprt>::const_iterator it=invariants.begin();
       it!=invariants.end();
       it++)
  {
    if(it->get_bool("#unconditional"))
    {
      goto_programt::targett assume(goto_program.add_instruction(ASSUME));
      assume->guard=*it;
      assume->labels.push_back("PRECONDITION");
    }
    else
    {
      irep_idt identifier="precondition_check$"+integer2string(counter++);
      irep_idt long_id = "loopfrog::" + identifier.as_string();

      symbolt *symbolp = NULL;
      contextt::symbolst::iterator s_it = context.symbols.find(identifier);

      if (s_it==context.symbols.end())
      {
        symbolt new_symbol;
        new_symbol.name=long_id;
        new_symbol.type=typet("bool");
        new_symbol.is_statevar=true;
        new_symbol.lvalue=true;
        new_symbol.static_lifetime=true;
        new_symbol.pretty_name=identifier;
        new_symbol.base_name=identifier;

        context.move(new_symbol, symbolp);
        assert(symbolp!=NULL);
      }
      else
      {
        symbolp = &s_it->second;
      }

      const symbolt &symbol = *symbolp;

      exprt flag_expr=symbol_expr(symbol);

      goto_programt::targett assign(goto_program.add_instruction(ASSIGN));
      assign->code=code_assignt(flag_expr, *it);
      assign->labels.push_back("PRECONDITION_CHECK");
    }
  }
}

/*******************************************************************\

 Function: loop_summaryt::get_invariants_program

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void loop_summaryt::get_invariants_program(
  contextt &context,
  goto_programt &goto_program)
{
  unsigned counter=0;

  for (std::set<exprt>::const_iterator it=invariants.begin();
       it!=invariants.end();
       it++)
  {
    if(it->get_bool("#unconditional"))
    {
      goto_programt::targett assume(goto_program.add_instruction(ASSUME));
      assume->guard=*it;
      assume->labels.push_back("INVARIANT");
    }
    else
    {
      irep_idt identifier="precondition_check$"+integer2string(counter++);
      irep_idt long_id = "loopfrog::" + identifier.as_string();

      symbolt *symbolp = NULL;
      contextt::symbolst::iterator s_it = context.symbols.find(identifier);

      if (s_it==context.symbols.end())
      {
        symbolt new_symbol;
        new_symbol.name=long_id;
        new_symbol.type=typet("bool");
        new_symbol.is_statevar=true;
        new_symbol.lvalue=true;
        new_symbol.static_lifetime=true;
        new_symbol.pretty_name=identifier;
        new_symbol.base_name=identifier;

        context.move(new_symbol, symbolp);
        assert(symbolp!=NULL);
      }
      else
      {
        symbolp = &s_it->second;
      }

      const symbolt &symbol = *symbolp;
      exprt flag_expr=symbol_expr(symbol);

      goto_programt::targett guard(goto_program.add_instruction(GOTO));
      goto_programt::targett assume(goto_program.add_instruction(ASSUME));
      goto_programt::targett skip(goto_program.add_instruction(SKIP));

      guard->make_goto(skip);
      guard->guard.swap(flag_expr);
      guard->guard.make_not();

      exprt assume_expr(*it);
      assume->guard.swap(assume_expr);
      assume->labels.push_back("INVARIANT");
    }
  }
}

/********************************************************************\

 Function: loop_summaryt::assign_nondet_rec

 Inputs:

 Outputs:

 Purpose: Does the recursive assignments of the operands in expression

 \*******************************************************************/

void loop_summaryt::assign_nondet_rec(
  const exprt &e,
  value_setst &value_sets,
  goto_programt &program) const
{
  if(e.id()=="index")
  {
    assert(e.operands().size()==2);

    assign_nondet_rec(e.op0(), value_sets, program);
  }
  else if(e.id()=="member")
  {
    assign_nondet_rec(e.op0(), value_sets, program);
  }
  else if (e.id()=="symbol")
  {
    goto_programt::targett t = program.add_instruction(ASSIGN);
    t->code=code_assignt(e, nondet_exprt(e.type()));

    if (find(t->labels.begin(), t->labels.end(), irep_idt("VARIANT"))
        ==t->labels.end())
      t->labels.push_back("VARIANT");
  }
  else if (e.id()=="byte_extract_little_endian" || e.id()
      =="byte_extract_big_endian")
  {
    assert(e.operands().size()==2);

    assign_nondet_rec(e.op0(), value_sets, program);
  }
  else if (e.id()==ID_if)
  {
    assert(e.operands().size()==3);

    assign_nondet_rec(e.op1(), value_sets, program);
    assign_nondet_rec(e.op2(), value_sets, program);
  }
  else if (e.id()=="typecast")
  {
    assert(e.operands().size()==1);

    assign_nondet_rec(e.op0(), value_sets, program);
  }
  else if (e.id()=="NULL-object" ||
  				 e.id()==ID_string_constant ||
  				 e.id()=="valid_object" ||
  				 e.id()=="invalid_object" ||
  				 e.id()=="zero_string")
  {
    // this is bad. no idea how to handle it.
    // let's ignore it.
//    std::cout << "IGNORED: " << e << std::endl;
  }
  else if(e.id()=="dereference")
  {
    goto_programt::targett t = program.add_instruction(ASSIGN);
    t->code=code_assignt(e, nondet_exprt(e.type()));

    value_setst::valuest values;
    value_sets.get_values(loop_head, e, values);

    for(value_setst::valuest::const_iterator it = values.begin();
        it!=values.end();
        it++)
    {
      if(it->id()!="unknown" &&
         it->id()!="invalid")
        assign_nondet_rec(*it, value_sets, program);
    }
  }
  else if(e.is_nil())
  {
    // ignore
//    std::cout << "IGNORED: " << e << std::endl;

  }
  else
    throw "Unhandled variant type: " + e.id_string();
}
