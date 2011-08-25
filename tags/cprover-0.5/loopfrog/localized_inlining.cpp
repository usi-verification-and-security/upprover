/*******************************************************************

 Module: Localized Inlining (Assertion dependent precision)

 Author: CM Wintersteiger

\*******************************************************************/

#include <goto-programs/remove_skip.h>
#include <util/base_type.h>
#include <message_stream.h>
#include <arith_tools.h>

#include "localized_inlining.h"

/*******************************************************************\

Function: goto_inline_localizedt::parameter_assignments

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_inline_localizedt::parameter_assignments(
  const locationt &location,
  const code_typet &code_type,
  const exprt::operandst &arguments,
  goto_programt &dest,
  std::ostream &out)
{
  // iterates over the operands
  exprt::operandst::const_iterator it1=arguments.begin();

  const code_typet::argumentst &argument_types=code_type.arguments();

  // iterates over the types of the arguments
  for(code_typet::argumentst::const_iterator
      it2=argument_types.begin();
      it2!=argument_types.end();
      it2++)
  {
    // if you run out of actual arguments there was a mismatch
    if(it1==arguments.end())
    {
      stream_message_handlert mh(out);
      message_streamt ms(mh);
      ms.err_location(location);
      ms.error("function call: not enough arguments");
      throw 0;
    }

    const exprt &argument=static_cast<const exprt &>(*it2);

    // this is the type the n-th argument should be
    const typet &arg_type=argument.type();

    const irep_idt &identifier=argument.get("#identifier");

    if(identifier=="")
    {
      stream_message_handlert mh(out);
      message_streamt ms(mh);
      ms.err_location(location);
      ms.error("no identifier for function argument");
      throw 0;
    }

    // nil means "don't assign"
    if(it1->is_nil())
    {
    }
    else
    {
      // this is the actual parameter
      exprt actual(*it1);

      // it should be the same exact type
      if(!base_type_eq(arg_type, actual.type(), ns))
      {
        // we are willing to do some conversion
        if((ns.follow(arg_type).id()=="signedbv" ||
            ns.follow(arg_type).id()=="unsignedbv" ||
            ns.follow(arg_type).id()=="bool") &&
           (ns.follow(actual.type()).id()=="signedbv" ||
            ns.follow(actual.type()).id()=="unsignedbv" ||
            ns.follow(actual.type()).id()=="bool"))
        {
          actual.make_typecast(arg_type);
        }
        else
        {
          stream_message_handlert mh(out);
          message_streamt ms(mh);
          ms.err_location(location);
          ms.str << "function call: argument `" << identifier
                 << "' type mismatch: got "
                 << from_type(ns, identifier, it1->type())
                 << ", expected "
                 << from_type(ns, identifier, arg_type);
          ms.error(ms.str.str());
          throw 0;
        }
      }

      // adds an assignment of the actual parameter to the formal parameter
      exprt assignment("code", typet("code"));
      assignment.set("statement", "assign");
      assignment.operands().resize(2);
      assignment.op0()=exprt("symbol", arg_type);
      assignment.op0().set("identifier", identifier);
      assignment.op1().swap(actual);
      assignment.location()=location;

      dest.add_instruction(ASSIGN);
      dest.instructions.back().location=location;
      dest.instructions.back().code.swap(assignment);
      dest.instructions.back().function=code_type.location().get_function();
    }

    it1++;
  }

//  if(it1!=arguments.end()) // too many arguments -- we just ignore that,
                             // no harm done

  if(code_type.get_bool("#hide"))
  {
    Forall_goto_program_instructions(h_it, dest)
    {
      h_it->location.id(""); // not NIL
      h_it->location.set_file(location.get_file());
      h_it->location.set_line(location.get_line());
      h_it->location.set_column(location.get_column());
      h_it->location.set_function(location.get_function());
    }
  }

  dest.add_instruction(END_FUNCTION); // make this look like a function
}

/*******************************************************************\

Function: goto_inline_localizedt::replace_return

  Inputs:

 Outputs:

 Purpose: turns returns into assignments to lhs

\*******************************************************************/

void goto_inline_localizedt::replace_return(
  goto_programt &dest,
  goto_programt::const_targett it,
  goto_programt::const_targett end_of_function,
  const exprt &lhs,
  std::ostream &out)
{
  assert(it->is_return());

  bool target_set=false;

  if(lhs.is_not_nil())
  {
    if(it->code.operands().size()!=1)
    {
      stream_message_handlert mh(out);
      message_streamt ms(mh);
      ms.err_location(it->code);
      ms.str << "return expects one operand!";
      ms.warning();
      return;
    }

    goto_programt::targett assignment=dest.add_instruction(ASSIGN);

    assignment->code=code_assignt(lhs, it->code.op0());
    assignment->location=it->location;
    assignment->function=it->location.get_function();

    progress.targets_mapping[it] = assignment; // for gotos that point to the return!
    target_set=true;
  }
  else if(!it->code.operands().empty())
  {
    goto_programt::targett expression=dest.add_instruction(OTHER);

    expression->code=codet("expression");
    expression->code.copy_to_operands(it->code.op0());
    expression->location=it->location;
    expression->function=it->location.get_function();

    progress.targets_mapping[it] = expression; // for gotos that point to the return!
    target_set=true;
  }

  goto_programt::targett go=dest.add_instruction(GOTO);
  if (!target_set) progress.targets_mapping[it] = go;

  // Yes, this is a really nasty cast. However, we only need
  // that goto-target to look up it's mapped target. This
  // should work in most STL implementations.
  void *tp = &end_of_function;
  goto_programt::targett newt = *((goto_programt::targett*)tp);

  go->targets.push_back(newt);
  progress.unresolved_gotos.push_back(go);
}

/*******************************************************************

 Function: goto_inline_localizedt::goto_inline_int

 Inputs:

 Outputs:

 Purpose: Inlines goto_program using imprecise loop summaries. Precise
          summaries are only used on the call path to the location.

 \*******************************************************************/

goto_programt::const_targett goto_inline_localizedt::goto_inline_int(
  const call_stackt &goal_stack,
  goto_programt::const_targett location,
  std::ostream &out)
{
  #if 0
  std::cout << "GOTO_INLINE_INT" << std::endl;
  #endif

  // We inline on the fly, while traversing the functions and
  // loop summaries. Any forward goto is remembered in
  // `unresolved_gotos' and resolved afterwards.

  goto_programt::const_targett it;

  if(progress.stack.empty())
  {
    progress.stack.push(inlining_contextt());
    inlining_contextt &top = progress.stack.top();
    top.return_lhs.make_nil();
    top.renaming_index = 0;
    top.function.id("symbol"); top.function.set("identifier", "main");
    top.goto_program = &progress.source_program;
    top.end_of_function = --progress.source_program.instructions.end();
    top.is_param_context = false;

    it = progress.source_program.instructions.begin();
  }
  else
  {
    it = progress.restart_target;

    goto_programt::targett last =
      progress.dest_program.instructions.end();
    last--;
    if(last->is_assert())
    {
      if(progress.keep_assertions)
        last->type=ASSUME;
      else
        last->make_skip();
    }
  }

  while(it!=progress.source_program.instructions.end() &&
        (it!=location ||
         progress.call_stack!=goal_stack))
  {
    #if 0
    {
      inlining_contextt &current_context = progress.stack.top();
      current_context.goto_program->output_instruction(ns, "", std::cout, it);
    }
    #endif

    if(it->is_function_call())
    {
      const code_function_callt &call=to_code_function_call(to_code(it->code));

      if(call.function().id()=="symbol")
      {
        const irep_idt &identifier=call.function().get("identifier");

        // check for recursions
        if(progress.recursion_set.find(identifier)!=
           progress.recursion_set.end())
        {
          stream_message_handlert mh(out);
          message_streamt ms(mh);
          ms.err_location(call.function());
          ms.warning("recursion is ignored");

          // but let's be nice to GOTOs...
          goto_programt::targett t=add_skip(progress.dest_program);
          progress.targets_mapping[it] = t;

          it++;
        }
        else
        {
          const goto_functionst::goto_functiont &f = find_function(call, out);

          if(f.body_available)
          {
            progress.recursion_set.insert(identifier);

            // add a target for any GOTOs that want to jump here
            goto_programt::targett t=add_skip(progress.dest_program);
            progress.targets_mapping[it] = t;

            // We first want to inline the parameter assignments,
            // and after that the function body. So we need to put them
            // on the stack in reverse order.

            #if 0
            std::cout << "Inlining " << identifier << std::endl;
            #endif

            // set up a new level for the actual function body
            progress.stack.push(inlining_contextt());
            inlining_contextt &body_context = progress.stack.top();
            body_context.return_lhs = call.lhs();
            body_context.renaming_index = ++total_renamings;
            body_context.function = call.function();
            body_context.goto_program = &f.body;
            body_context.end_of_function =
              --body_context.goto_program->instructions.end();
            body_context.is_param_context = false;

            progress.call_stack.push(it);

            #if 0
            std::cout << "Inlining parameters" << std::endl;
            #endif

            // and another one for the parameter assignments
            progress.stack.push(inlining_contextt());
            inlining_contextt &param_context = progress.stack.top();

            param_context.return_lhs = call.lhs(); // same as above!
            param_context.renaming_index = total_renamings; // same as above!
            param_context.function = irept(); // no name!

            // get a new temporary
            progress.temporary_programs.push_front(goto_programt());
            param_context.goto_program = &progress.temporary_programs.back();
            parameter_assignments(
                body_context.goto_program->instructions.front().location,
                f.type,
                call.arguments(),
                progress.temporary_programs.back(),
                out);
            param_context.end_of_function =
              --body_context.goto_program->instructions.end(); // same as above!
            param_context.is_param_context = true;

            progress.call_stack.push(
                body_context.goto_program->instructions.begin());

            it = param_context.goto_program->instructions.begin();
          }
          else
          {
            // we don't have a function body, but still we got to do some work.
            stream_message_handlert mh(out);
            message_streamt ms(mh);
            ms.err_location(call.function());
            ms.str << "no body for function `" << identifier << "'";
            ms.warning();

            // add a target for any GOTOs that want to jump here
            goto_programt::targett t=add_skip(progress.dest_program);
            progress.targets_mapping[it] = t;

            // We don't need a context for this,
            // let's just add the according instructions.

            forall_expr(e_it, call.arguments())
            {
              goto_programt::targett t=
                progress.dest_program.add_instruction();
              t->make_other();
              t->location=it->location;
              t->function=it->location.get_function();
              t->code=codet("expression");
              t->code.copy_to_operands(*e_it);
            }

            // return value
            const exprt &lhs = call.lhs();
            if(lhs.is_not_nil())
            {
              exprt rhs=exprt("sideeffect", lhs.type());
              rhs.set("statement", "nondet");
              rhs.location()=it->location;

              code_assignt code(lhs, rhs);
              code.location()=it->location;

              goto_programt::targett t=
                progress.dest_program.add_instruction(ASSIGN);
              t->location=it->location;
              t->function=it->location.get_function();
              t->code.swap(code);
            }

            it++;
          }
        }
      }
      else
        throw "non-symbol function call";
    }
    else if(it->is_return())
    {
      inlining_contextt &current_context = progress.stack.top();
      replace_return(progress.dest_program, it,
                     current_context.end_of_function,
                     current_context.return_lhs,
                     out);
      it++; // just look at the next one
    }
    else if(it->is_end_function())
    {
      #if 0
      std::cout << "Popping" << std::endl;
      #endif

      // some return-GOTOs might point here!
      goto_programt::targett newt = add_skip(progress.dest_program);
      progress.targets_mapping[it] = newt;

      inlining_contextt &current_context = progress.stack.top();

      goto_programt::const_targett real_end =
        current_context.goto_program->instructions.end();

      progress.targets_mapping[real_end] = newt;

      resolve_gotos();

      // we're exiting from a program:
      // all the goto mappings are now invalidated, which is fine!
      for(goto_programt::const_targett i_it =
            current_context.goto_program->instructions.begin();
          i_it!=current_context.goto_program->instructions.end();
          i_it++)
      {
        progress.targets_mapping.erase(i_it);
      }
      progress.targets_mapping.erase(real_end);

      progress.recursion_set.erase(current_context.function.get("identifier"));
      remove_temporary_program(current_context.goto_program);

      it = progress.call_stack.top();
      if(!current_context.is_param_context)
        it++; // we saved the call

      progress.stack.pop();
      progress.call_stack.pop();

      #if 0
      std::cout << "Stack Size: " << progress.stack.size() << std::endl;
      #endif

      if(progress.stack.empty()) break;
    }
    else // any other instruction
    {
      if(it->is_other() &&
         it->code.get("statement")=="loop-summary")
      {
        const codet &code = to_code(it->code);
        std::string ident = "LOOP-SUMMARY-" + code.get("index").as_string();

        if(progress.recursion_set.find(ident)!=
           progress.recursion_set.end())
        {
          throw "LOOP RECURSION!";
        }
        else
        {
          progress.recursion_set.insert(ident);
          inlining_contextt &current_context = progress.stack.top();

          // we need a GOTO target
          goto_programt::targett t=add_skip(progress.dest_program);
          progress.targets_mapping[it] = t;

          progress.call_stack.push(it);

          #if 0
            std::cout << "Inlining Loop Summary #" << inx << std::endl;
          #endif

          // we want precise summaries if the assertion is in that summary,
          // and when the loop is on the same level as the assertion.
          bool full = is_prefix_of(progress.call_stack, goal_stack) ||
                      (goal_stack.size()+1==progress.call_stack.size() &&
                       is_prefix_of(goal_stack, progress.call_stack));

          mp_integer inx_mp = string2integer(code.get("index").as_string(), 10);
          unsigned long inx = inx_mp.to_ulong();

          #if 0
          if(full) std::cout << "FULL" << std::endl;
          else std::cout << "SIMPLE" << std::endl;

          std::cout << "CALL STACK: ";
          for(call_stackt::const_iterator l_it=progress.call_stack.begin();
              l_it!=progress.call_stack.end();
              l_it++)
            std::cout << (unsigned) &(**l_it) << " ";
          std::cout << std::endl;

          std::cout << "GOAL STACK: ";
          for(call_stackt::const_iterator l_it=goal_stack.begin();
              l_it!=goal_stack.end();
              l_it++)
            std::cout << (unsigned) &(**l_it) << " ";
          std::cout << std::endl;
          #endif

          if(full)
          {
            // set up a new level for the precise loop body
            progress.stack.push(inlining_contextt());
            inlining_contextt &body_context = progress.stack.top();
            body_context.return_lhs = current_context.return_lhs; // keep
            body_context.renaming_index = current_context.renaming_index; // keep
            body_context.function = irept("symbol");
            body_context.function.set("identifier", ident);
            body_context.end_of_function =
              current_context.end_of_function; // keep
            body_context.is_param_context = false;

            loopstoret::const_iterator sprec_it = precise_loops.find(inx);
            if(sprec_it==precise_loops.end())
              throw "Invalid loop-summary index";

            body_context.goto_program = &sprec_it->second;

            progress.call_stack.push(
                             body_context.goto_program->instructions.begin());
          }

          // set up a new level for the imprecise summary
          progress.stack.push(inlining_contextt());
          inlining_contextt &imp_context = progress.stack.top();
          imp_context.return_lhs = current_context.return_lhs; // keep
          imp_context.renaming_index = current_context.renaming_index; // keep
          imp_context.function = irept("symbol");
          imp_context.function.set("identifier", ident);
          imp_context.end_of_function =
            current_context.end_of_function; // keep
          imp_context.is_param_context = full;


          loopstoret::const_iterator simprec_it = imprecise_loops.find(inx);
          if(simprec_it==imprecise_loops.end())
            throw "Invalid loop-summary index";

          imp_context.goto_program = &simprec_it->second;

          it = imp_context.goto_program->instructions.begin();
        }
      }
      else
      {
        // just copy
        goto_programt::targett new_instruction=add_skip(progress.dest_program);

        if(it->is_goto())
        {
          *new_instruction=*it;
          assert(progress.targets_mapping.find(it)==
                 progress.targets_mapping.end());
          progress.unresolved_gotos.push_back(new_instruction);
        }
        else if(it->is_assert())
        {
          if(progress.keep_assertions)
          {
            *new_instruction=*it;
            new_instruction->type=ASSUME;
          }
          else
            new_instruction->type=SKIP;
        }
        else
          *new_instruction=*it;

        progress.targets_mapping[it]=new_instruction;

        it++; // proceed to the next instruction
      }
    }
  }

  if(it!=progress.source_program.instructions.end())
  {
    // the last instruction is special
    goto_programt::targett new_instruction=
      progress.dest_program.add_instruction();
    progress.targets_mapping[it]=new_instruction;
    *new_instruction=*it;

    // save restart target
    goto_programt::const_targett location_next = location; location_next++;
    progress.restart_target = location_next;

    return new_instruction;
  }
  else
    return progress.source_program.instructions.end();
}

/*******************************************************************

 Function: goto_inline_localizedt::add_skip

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

goto_programt::targett goto_inline_localizedt::add_skip(
  goto_programt &program)
{
  goto_programt::targett last = --program.instructions.end();

  if(program.instructions.size()==0 &&
      last->type==SKIP &&
      last->labels.empty())
    return last;
  else
    return program.add_instruction(SKIP);
}

/*******************************************************************

 Function: goto_inline_localizedt::goto_inline

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

goto_programt::const_targett goto_inline_localizedt::goto_inline(
  const call_stackt &goal_stack,
  goto_programt::const_targett location,
  std::ostream &out)
{
  goto_programt::const_targett new_location =
    goto_inline_int(goal_stack, location, out);

  resolve_gotos();
  cut_unresolved_gotos();
  progress.dest_program.update();

  return new_location;
}

/*******************************************************************

 Function: find_assertion

 Inputs:

 Outputs:

 Purpose: Starting from `start' we search for an assertion.
          `stack' keeps the call path to that assertion.

 \*******************************************************************/

goto_programt::const_targett find_assertion(
  const goto_programt::const_targett &start,
  const goto_functionst &goto_functions,
  const loopstoret &imprecise_loops,
  const loopstoret &precise_loops,
  call_stackt &stack)
{
  goto_programt::const_targett it = start; it++;

  while(it->type!=ASSERT)
  {
    if(it->type==FUNCTION_CALL)
    {
      const code_function_callt &call =
        to_code_function_call(to_code(it->code));

      const irep_idt &name = call.function().get("identifier");

      goto_functionst::function_mapt::const_iterator f_it =
        goto_functions.function_map.find(name);

      if(f_it!=goto_functions.function_map.end() &&
         f_it->second.body.instructions.size()>0)
      {
        stack.push(it);
        it = f_it->second.body.instructions.begin();
      }
      else
        it++; // just ignore it
    }
    else if(it->type==OTHER)
    {
      if(it->is_other() &&
         it->code.get("statement")=="loop-summary")
      {
        const codet &code = to_code(it->code);
        mp_integer inx_mp = string2integer(code.get("index").as_string(), 10);
        unsigned long inx = inx_mp.to_ulong();

        // always search the precise loops
        loopstoret::const_iterator s_it = precise_loops.find(inx);

        if(s_it==precise_loops.end())
          throw "Invalid loop-summary index";
        else
        {
          stack.push(it);
          it = s_it->second.instructions.begin();
        }
      }
      else
        it++;
    }
    else if(it->type==END_FUNCTION)
    {
      if(stack.size()==0)
      {
        // this must be the end.
        return (++it);
      }
      else
      {
        it = stack.top(); stack.pop();
        it++;
      }
    }
    else
      it++;
  }

  // `it' now points to the assertion, while
  // stack contains the call stack for this assertion
  return it;
}

/*******************************************************************

 Function: find_assertion_n

 Inputs:

 Outputs:

 Purpose: finds the n'th assertion

 \*******************************************************************/

goto_programt::const_targett find_assertion_n(
  const goto_programt::const_targett &start,
  const goto_functionst &goto_functions,
  const loopstoret &imprecise_loops,
  const loopstoret &precise_loops,
  unsigned n)
{
  call_stackt stack;
  goto_programt::const_targett res=start;

  unsigned i=0;
  do {
    res = find_assertion(res,
                         goto_functions,
                         imprecise_loops,
                         precise_loops,
                         stack);
    i++;
  } while (i<n);

  return res;
}

/*******************************************************************

 Function: find_assertion_n

 Inputs:

 Outputs:

 Purpose: finds the n'th assertion

 \*******************************************************************/

goto_programt::const_targett find_assertion_n(
  const goto_programt::const_targett &start,
  const goto_functionst &goto_functions,
  const loopstoret &imprecise_loops,
  const loopstoret &precise_loops,
  call_stackt &stack,
  unsigned n)
{
  goto_programt::const_targett res=start;

  unsigned i=0;
  do {
    res = find_assertion(res,
                         goto_functions,
                         imprecise_loops,
                         precise_loops,
                         stack);
    i++;
  } while (i<n);

  return res;
}

/*******************************************************************

 Function: goto_inline_localizedt::resolve_gotos

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void goto_inline_localizedt::resolve_gotos( void )
{
  progress.dest_program.compute_location_numbers();

  unresolved_gotost::iterator it = progress.unresolved_gotos.begin();
  while(it!=progress.unresolved_gotos.end())
  {
    goto_programt::instructiont &i = **it;

    bool all_resolved = true;

    goto_programt::targetst &targets=(i.is_assume()) ? // disabled goto?
                                       progress.disabled_goto_targets[*it]  :
                                       i.targets;

    for(goto_programt::targetst::iterator t_it = targets.begin();
        t_it!=targets.end();
        t_it++)
    {
      targets_mappingt::const_iterator m_it =
        progress.targets_mapping.find(*t_it);

      if(m_it!=progress.targets_mapping.end())
      {
        assert(m_it->second->location_number > i.location_number);
        *t_it = m_it->second;
      }
      else
        all_resolved = false;
    }


    if(all_resolved)
    {
      if(i.is_assume()) // this has been disabled before
        enable_goto(*it);

      it = progress.unresolved_gotos.erase(it);
    }
    else
      it++;
  }
}

/*******************************************************************

 Function: goto_inline_localizedt::cut_unresolved_gotos

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void goto_inline_localizedt::cut_unresolved_gotos( void )
{
  #if 0
  std::cout << unresolved_gotos.size() << " unresolved GOTOs." << std::endl;
  #endif

  for(unresolved_gotost::iterator it=progress.unresolved_gotos.begin();
      it!=progress.unresolved_gotos.end();
      it++)
  {
    if((*it)->is_goto()) // otherwise it's disabled already
      disable_goto(*it);
  }
}

/*******************************************************************

 Function: goto_inline_localizedt::find_function

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

const goto_functionst::goto_functiont &goto_inline_localizedt::find_function(
  const code_function_callt &call,
  std::ostream &out)
{
  const irep_idt &identifier=call.function().get("identifier");

  // find the function
  goto_functionst::function_mapt::const_iterator m_it=
    goto_functions.function_map.find(identifier);

  if(m_it==goto_functions.function_map.end())
  {
    stream_message_handlert mh(out);
    message_streamt ms(mh);
    ms.err_location(call.function());
    ms.str << "failed to find function `" << identifier << "'";
    ms.error(ms.str.str());
    throw 0;
  }

  return m_it->second;
}

/*******************************************************************

 Function: goto_inline_localizedt::remove_temporary_program

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void goto_inline_localizedt::remove_temporary_program(
  const goto_programt *program)
{
  for(temporary_programst::iterator it = progress.temporary_programs.begin();
      it!=progress.temporary_programs.end();
      ) // no inc
  {
    if(&(*it)==program)
    {
      it = progress.temporary_programs.erase(it);
      break; // there won't be a second one...
    }
    else
      it++;
  }
}

/*******************************************************************

 Function: goto_inline_localizedt::is_prefix_of

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool goto_inline_localizedt::is_prefix_of(
  const call_stackt &left,
  const call_stackt &right)
{
  if(left.size()>right.size()) return false;

  call_stackt::const_iterator l_it=left.begin();
  call_stackt::const_iterator r_it=right.begin();

  while(l_it!=left.end())
  {
    if(*l_it!=*r_it) return false;
    l_it++; r_it++;
  }

  return true;
}

/*******************************************************************

 Function: goto_inline_localizedt::enable_goto

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void goto_inline_localizedt::enable_goto(goto_programt::targett target)
{
  assert(target->type==ASSUME);

  target->type=GOTO;
  target->guard.make_not();

  goto_programt::instructiont::labelst::iterator l_it=
    find(target->labels.begin(), target->labels.end(), "DISABLED_GOTO");
  assert(l_it!=target->labels.end());
  target->labels.erase(l_it);

  disabled_goto_targetst::iterator t_it=
    progress.disabled_goto_targets.find(target);
  assert(t_it!=progress.disabled_goto_targets.end());

  target->targets.swap(t_it->second);
}

/*******************************************************************

 Function: goto_inline_localizedt::disable_goto

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void goto_inline_localizedt::disable_goto(goto_programt::targett target)
{
  assert(target->type==GOTO);

  target->labels.push_back("DISABLED_GOTO");
  target->type = ASSUME;
  target->guard.make_not();

  assert(progress.disabled_goto_targets.find(target)==
         progress.disabled_goto_targets.end());

  progress.disabled_goto_targets[target].swap(target->targets);
  target->targets.clear();
}

/*******************************************************************

 Function: goto_inline_localizedt::check_targets

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool goto_inline_localizedt::check_targets(goto_programt &program) const
{
  bool res=true;

  // check that all goto targets point into the same program
  forall_goto_program_instructions(it, program)
  {
    program.output_instruction(ns, "", std::cout, it);
    for(goto_programt::targetst::const_iterator tit=it->targets.begin();
        tit!=it->targets.end();
        tit++)
    {
      bool found=false;
      forall_goto_program_instructions(fit, program)
      {
        if(fit==*tit)
        {
          found=true;
          res=false;
          break;
        }
      }
      assert(found);
    }
  }

  return res;
}
