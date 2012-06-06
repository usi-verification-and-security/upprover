/*******************************************************************\

Module: Termination instrumentation

Author: CM Wintersteiger

\*******************************************************************/

#include <ansi-c/expr2c.h>

#include <std_expr.h>
#include <expr_util.h>
#include <i2string.h>
#include <rename.h>
#include <prefix.h>

#include "instrumentation.h"

/*******************************************************************\

Function: termination_instrumentert::termination_instrumentert

  Inputs:

 Outputs:

 Purpose: Constructor

\*******************************************************************/

termination_instrumentert::termination_instrumentert(
  goto_functionst &_gf,
  contextt &_ct,
  message_handlert &_mh,
  modet _mode) :
    messaget(_mh),
    goto_functions(_gf),
    context(_ct),
    ns(_ct),
    mode(_mode),
    loop_counter(0),
    tmp_symbol_cnt(0)
{
}

/*******************************************************************\

Function: termination_instrumentert::~termination_instrumentert

  Inputs:

 Outputs:

 Purpose: Destructor

\*******************************************************************/

termination_instrumentert::~termination_instrumentert()
{
}

/*******************************************************************\

Function: termination_instrumentert::instrument

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned termination_instrumentert::instrument(
  goto_programt &program, 
  bool copy_state)
{
  unsigned res=0;
  
  // remove all assertions from the program
  Forall_goto_program_instructions(it, program)
    if(it->is_assert())
      it->type=SKIP;

  // find loops
  for(goto_programt::targett
      it=program.instructions.begin();
      it!=program.instructions.end();
      ) // no it++
  {
    // do this now, the program changes!
    goto_programt::targett next=it;
    next++;

    if(it->is_goto())
    {
      if(it->is_backwards_goto())
      {
        assert(it->targets.size()==1);
        loopt loop;
        loop.begin=it->targets.front();
        loop.end=it;
        instrument_loop(loop, program, copy_state);
        res+=1;
      }
    }

    it=next;
  }
  
  return res;
}

/*******************************************************************\

Function: termination_instrumentert::instrument

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned termination_instrumentert::instrument(bool copy_state)
{
  goto_functions.compute_loop_numbers();
  unsigned total=0;
  
  Forall_goto_functions(it, goto_functions)
  {
    if(it->second.body_available)
      total+=instrument(it->second.body, copy_state);
  }
  
  return total;
}

/*******************************************************************\

 Function: termination_instrumentert::get_variant

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void termination_instrumentert::get_variant(
  loopt &loop,
  bool only_globals)
{
  for(goto_programt::const_targett it=loop.begin; it!=loop.end; it++)
  {
    switch(it->type)
    {
    case FUNCTION_CALL:
      {
        const code_function_callt &call=to_code_function_call(it->code);        
        const irep_idt &fid=call.function().get(ID_identifier);
        
        if(only_globals)
          add_globals(call.lhs(), loop.variant);
        else
          find_symbols(call.lhs(), loop.variant);

        globals_cachet::const_iterator cit=globals_cache.find(fid);
        
        if(cit==globals_cache.end())
        {
          const goto_functionst::function_mapt::iterator fit=
              goto_functions.function_map.find(fid);

          if(fit!=goto_functions.function_map.end())
          {
            loopt function;
            function.begin=fit->second.body.instructions.begin();
            function.end=fit->second.body.instructions.end();
            
            globals_cache[fid].clear(); // avoid recursion
            get_variant(function, true);
            loop.variant.insert(function.variant.begin(), function.variant.end());
            globals_cache[fid].swap(function.variant); // save
          } 
        }
        else // cached
        {
          loop.variant.insert(cit->second.begin(), cit->second.end());
        }
      }
      break;

    case ASSIGN:
    {
      const code_assignt &code=to_code_assign(it->code);

      add_globals(code.lhs(), loop.variant);

      if(!only_globals)
        find_symbols(code.lhs(), loop.variant);
      
      break;
    }

    default: break; /* Nothing */
    }
  }

  #if 0
  std::cout << "VARIANT: " << std::endl;
  for(find_symbols_sett::const_iterator
      it=loop.variant.begin();
      it!=loop.variant.end();
      it++)
  {
    std::cout << *it << std::endl;
  }
  #endif
}

/*******************************************************************\

 Function: termination_instrumentert::add_copied_flag

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt termination_instrumentert::add_copied_flag(
  loopt &loop, 
  goto_programt &program)
{
  unsigned loop_id=loop.end->loop_number;

  // add a flag
  std::string flag_ident;
  
  switch(mode)
  {
    case T_RANKSYNTH:
      flag_ident = "termination::copied_"+i2string(loop_id);
      break;
    case T_DIRECT:
      flag_ident = "termination::saved_"+i2string(loop_id);
      break;
    default:
      throw ("UNKNOWN INSTRUMENTATION MODE");
  }

  symbolt flag_symbol;

  flag_symbol.name=flag_ident;
  flag_symbol.base_name=flag_ident.substr(flag_ident.find("::")+2);
  flag_symbol.type=bool_typet();
  flag_symbol.lvalue=true;
  exprt copied_flag=symbol_expr(flag_symbol);
  
  goto_programt::targett declins=
      program.insert_before(program.instructions.begin());
  
  declins->make_decl();
  declins->code=code_declt(copied_flag);
  
  context.move(flag_symbol);
  
  return copied_flag;
}

/*******************************************************************\

 Function: termination_instrumentert::instrument_loop

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void termination_instrumentert::instrument_loop(
  loopt &loop,
  goto_programt &program,
  bool copy_state)
{  
  get_variant(loop, false);

  #if 0
  std::cout << "VARIANT: " << std::endl;
  for(find_symbols_sett::const_iterator
      it=loop.variant.begin();
      it!=loop.variant.end();
      it++)
  {
    std::cout << *it << std::endl;
  }
  #endif
  
  // create old/new variables
  var_mapt var_map;
  
  if(!copy_state)
  {
    // just insert a dummy assertion
    goto_programt::instructiont assertion;    
    assertion.make_assertion(true_exprt());
    assertion.location=loop.begin->location;
    assertion.location.set("comment", "loop termination");
    assertion.location.set("property", "termination");
    
    program.insert_before_swap(loop.begin, assertion);
  }
  else
  {
    if(make_old_variables(loop, program, var_map))
    {
      // obsolete code: make_old_variables always returns false
      goto_programt::targett a=program.insert_before(loop.begin);
      a->type=ASSERT;
      a->guard=false_exprt(); // give up on loops over pointers
      a->location=loop.begin->location;
      a->location.set("comment", "loop termination");
      a->location.set("property", "termination");
    }
    else
    {
      // add the loop flag
      exprt cflag = add_copied_flag(loop, program);
  
      // set loop flag to false before entering
      goto_programt::targett set_flag=program.insert_before(loop.begin);
      set_flag->type=ASSIGN;
      set_flag->code=code_assignt(cflag, false_exprt());
      set_flag->location=loop.begin->location;
  
      // add termination assertion
      insert_assertion(loop, cflag, var_map, program);
  
      // all forwards-incoming edges of the loop head have to hit set_flag,
      // while all backwards-incoming edges have to hit the assertion!
      program.compute_incoming_edges();
  
      goto_programt::targett next=set_flag; next++;
  
      for(std::set<goto_programt::targett>::iterator it=
            next->incoming_edges.begin();
          it!=next->incoming_edges.end();
          it++)
      {
        if((*it)!=loop.end && (*it)->is_goto())
        {
          assert((*it)->targets.size()==1);
  
          if((*it)->targets.front()==next)
          {
            (*it)->targets.clear();
            (*it)->targets.push_back(set_flag);
          }
        }
      }
    }
  }
  
  loop_counter++;
}

/*******************************************************************\

 Function: termination_instrumentert::make_old_variables

 Inputs:

 Outputs:

 Purpose: create old/new variables

\*******************************************************************/

bool termination_instrumentert::make_old_variables(
  loopt &loop,
  goto_programt &program,
  var_mapt &var_map)
{
  unsigned loop_id=loop.end->loop_number;
  std::string prefix="termination::pre::"+i2string(loop_id)+"::";

  for(find_symbols_sett::const_iterator
      it=loop.variant.begin();
      it!=loop.variant.end();
      it++)
  {    
    const irep_idt &ident=*it;
    symbolt new_symbol;
        
    const symbolt &old_symbol=ns.lookup(ident);
    new_symbol=old_symbol;
        
    new_symbol.name=prefix+id2string(ident);
    new_symbol.base_name=old_symbol.base_name.as_string() + "'";
    new_symbol.pretty_name=old_symbol.pretty_name.as_string() + "'";    
    
    var_map[ident]=new_symbol.name;    
    
    goto_programt::targett declins=
        program.insert_before(program.instructions.begin());
    
    declins->make_decl();
    declins->code=code_declt(symbol_expr(new_symbol));
    context.move(new_symbol);
  }

  return false;
}

/*******************************************************************\

 Function: termination_instrumentert::generate_termination_assertion

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt termination_instrumentert::generate_termination_assertion(
  const exprt &copied_flag,
  const var_mapt &var_map) const
{
  exprt::operandst op;

  switch(mode)
  {
    case T_RANKSYNTH:
      // The most basic solution: start with `false'
      op.push_back(false_exprt());
      break;
    case T_DIRECT:
      // We need to check if the save state is equal to the current one.      
      for(var_mapt::const_iterator
          it=var_map.begin();
          it!=var_map.end();
          it++)
      {
        binary_relation_exprt bin(
                          symbol_exprt(it->first, ns.lookup(it->first).type), 
                          "=", 
                          symbol_exprt(it->second, ns.lookup(it->second).type));
        op.push_back(not_exprt(bin));
      }
      break;
    default:
      throw "UNKNOWN INSTRUMENTATION MODE";
  }

  return implies_exprt(copied_flag, or_exprt(op));  
}

/*******************************************************************\

 Function: termination_instrumentert::insert_assertion

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void termination_instrumentert::insert_assertion(
  loopt &loop,
  const exprt &copied_flag,
  const var_mapt &var_map,
  goto_programt &program)
{
  goto_programt dest;

  // build assertion
  goto_programt::targett a=dest.add_instruction(ASSERT);
  a->guard=generate_termination_assertion(copied_flag, var_map);

  // new nondet symbol
  symbolt ndsym;
  ndsym.name = "c::main::nondet_" + i2string(++tmp_symbol_cnt);
  ndsym.base_name = "nondet_" + i2string(tmp_symbol_cnt);
  ndsym.type = bool_typet();
  ndsym.lvalue=true;
  
  exprt nns = symbol_expr(ndsym);
  
  goto_programt::targett decl_statement=
      dest.add_instruction(DECL);
  decl_statement->code=code_declt(nns);
  
  // build branch
  exprt guard=or_exprt(copied_flag,nns);
  
  context.move(ndsym);  

  goto_programt::targett goto_statement=
    dest.add_instruction(GOTO);
  goto_statement->guard=guard;

  goto_programt::targett assign_copied=dest.add_instruction(ASSIGN);
  assign_copied->code=code_assignt(copied_flag, true_exprt());

  // copy the variables
  for(var_mapt::const_iterator
      it=var_map.begin();
      it!=var_map.end();
      it++)
  {
    goto_programt::targett v_assign=dest.add_instruction(ASSIGN);    
    v_assign->code=code_assignt(
                        symbol_exprt(it->second, ns.lookup(it->second).type), 
                        symbol_exprt(it->first, ns.lookup(it->first).type));
  }

  goto_programt::targett skip=dest.add_instruction(SKIP);
  goto_statement->targets.push_back(skip);

  // set locations
  Forall_goto_program_instructions(it, dest)
  {
    it->location=loop.begin->location;
    it->function=loop.begin->function;
  }

  // set comments for assertion
  a->location.set("comment", "loop termination");
  a->location.set("property", "termination");

  program.insert_before_swap(loop.begin, dest);
}

/*******************************************************************\

 Function: termination_instrumentert::is_global

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool termination_instrumentert::is_global(const irep_idt &ident) const
{
  const symbolt &symbol=ns.lookup(ident);
            
  return (symbol.lvalue && symbol.static_lifetime);
}

/*******************************************************************\

 Function: termination_instrumentert::add_globals

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void termination_instrumentert::add_globals(
  const exprt &expr,
  find_symbols_sett &dest) const
{
  find_symbols_sett temp;
  find_symbols(expr, temp);
  
  for(find_symbols_sett::const_iterator it=temp.begin(); it!=temp.end(); it++)
  {
    const irep_idt &ident=*it;
    
    if(is_global(ident))
      dest.insert(ident);
  } 
}
