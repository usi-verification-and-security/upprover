/*******************************************************************\

Module: Termination module: Compositional Termination Analysis

Author: CM Wintersteiger

\*******************************************************************/

#include "termination_cta.h"

#include <limits.h>
#include <sstream>
#include <fstream>

#include <std_expr.h>
#include <i2string.h>
#include <prefix.h>
#include <replace_symbol.h>
#include <simplify_expr.h>
#include <rename.h>

#include <goto-programs/invariant_propagation.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/wp.h>

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>

#include <goto-symex/symex_target_equation.h>
#include <goto-symex/goto_symex_state.h>
#include <goto-symex/basic_symex.h>
#include <goto-symex/goto_symex.h>
#include <goto-symex/build_goto_trace.h>

#include "termination_cta.h"
#include "termination_slicer.h"
#include "ranking.h"
#include "find_symbols_rw.h"
#include "replace_identifier.h"

/********************************************************************\

 Function: termination_ctat::terminates

 Inputs:

 Outputs:

 Purpose: Perform Termination Check for one specific loop

\********************************************************************/

termination_resultt termination_ctat::terminates(
  const irep_idt &main,
  const goto_functionst &goto_functions,
  goto_programt::const_targett assertion)
{  
  goto_programt::targett sliced_backjump;  

  sliced_goto_functions.clear();
  
  if(!get_model(main, goto_functions, assertion))
  {
    status("Slicer has shown unreachability of the assertion.");
    return T_TERMINATING;
  }  

  sliced_backjump=sliced_assertion;
  while(!sliced_backjump->is_backwards_goto()) sliced_backjump++;

  goto_programt::const_targett loop_end, loop_begin, copy_goto;
  get_loop_extent(sliced_assertion, loop_begin, loop_end, copy_goto);

  // get a mapping between pre and post variables
  replace_idt premap;
  get_pre_post_mapping(loop_begin, loop_end, premap);

  assert(loop_end->function!="");

  // clear the cache;
  // all those functions from other loops are not likely to work
  ranking_relations.clear();

  if(verbosity>6)
  {
    std::stringstream ss;

    const irep_idt &function=loop_end->function;
    goto_functionst::function_mapt::const_iterator f_it=
        sliced_goto_functions.function_map.find(function);
    assert(f_it!=sliced_goto_functions.function_map.end());
    const goto_programt &prog=f_it->second.body;
    for(goto_programt::const_targett it=loop_begin;
        it!=loop_end;
        it++)
      prog.output_instruction(ns, "", ss, it);
    prog.output_instruction(ns, "", ss, loop_end);
    debug(ss.str());
  }

  std::string u_mode="none";
  if(cmdline.isset("unranked-method"))
    u_mode=cmdline.getval("unranked-method");

  termination_resultt res=rank(loop_begin, sliced_backjump, copy_goto, 
                               premap, ranking_relations);

  if(res==T_NONTERMINATING && u_mode!="none")
  {
    if(u_mode=="precondition" || u_mode=="bmc-precondition")
      return T_NONTERMINATING;
    else
    {
      if(u_mode!="cegar" && u_mode!="bmc")
        throw "Unknown unranked-method";

      // The loop is non-terminating, and we don't know about the preconditions.
      // We need to check if this is reachable.

      if(!is_reachable(loop_begin, loop_end, u_mode=="bmc"))
      {
        status("Loop is potentially non-terminating, but unreachable.");
        res=T_TERMINATING;
      }
      else
        status("Loop is potentially non-terminating and reachable.");
    }
  }

  return res;
}

/********************************************************************\

 Function: termination_ctat::rank

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

termination_resultt termination_ctat::rank(
  goto_programt::const_targett &loop_begin,
  goto_programt::targett &sliced_backjump,
  goto_programt::const_targett &copy_goto,  
  replace_idt &premap,
  ranking_relation_cachet &ranking_relations)
{
  const irep_idt main_backup_id="termination::main$original";
  unsigned n=1;
  int delta=INT_MAX;
  termination_resultt res=T_UNKNOWN;

  concrete_modelt tainted_model(ns, temp_goto_functions);
  
  while(res==T_UNKNOWN)
  {
    unsigned before=ranking_relations.size();
    goto_programt::targett assertion;

    switch(n)
    {
      case 1:
        unwinding_init(main_backup_id, loop_begin, sliced_backjump, copy_goto,
                       assertion);
        break;

      default:
        unwinding_next(loop_begin, sliced_backjump, assertion, n);
        break;
    }

    std::stringstream msg;
    msg << "Generating ranking functions for " << n << " loop iteration"
        << ((n==1)?"":"s") << ".";
    status(msg.str());
    
    if(verbosity>8)
    {
      std::stringstream msg;
      msg << "Unwinding: " << std::endl;
      goto_functionst::function_mapt::const_iterator f_it = 
          temp_goto_functions.function_map.find(ID_main);
      assert(f_it!=temp_goto_functions.function_map.end());
      const goto_programt &f=f_it->second.body;
      f.output(ns, "", msg);
      debug(msg.str());
    }

    if(!rank_block(tainted_model, sliced_assertion, sliced_backjump, assertion,
                   premap, ranking_relations, main_backup_id))
      res=T_NONTERMINATING;
    else
    {
      delta=ranking_relations.size()-before;
      assert(delta>=0);
      status("Found " + i2string(delta) + " new ranking functions.");
            
      if(ranking_relations.is_compositional())        
      {
        status("Ranking argument is compositional.");
        res = T_TERMINATING;
      }
      else if (make_compositional(loop_begin, sliced_backjump, copy_goto,
                                  sliced_assertion, tainted_model, premap,
                                  ranking_relations)) 
      {
        // assert(ranking_relations.is_compositional());
        status("Ranking argument was made compositional.");
        res = T_TERMINATING;
      }
      else
      {
        status("Ranking argument is not compositional, "
               "increasing the unwinding.");
        n+=n;
      }
    }
  }

  unwinding_cleanup(main_backup_id);

  return res;
}

/********************************************************************\

 Function: termination_ctat::rename_main

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void termination_ctat::rename_main(const irep_idt &main_backup_id)
{
  temp_goto_functions.copy_from(sliced_goto_functions);
  
  // rename main
  goto_functionst::function_mapt::iterator main_it=
      temp_goto_functions.function_map.find("main");

  assert(main_it!=temp_goto_functions.function_map.end());

  goto_functionst::goto_functiont &main_backup=
      temp_goto_functions.function_map[main_backup_id];

  main_backup.swap(main_it->second);

  symbolst::const_iterator sit=context.symbols.find("main");
  symbolt ns=sit->second;
  ns.name=main_backup_id;
  ns.base_name=ns.name;
  ns.type=sit->second.type;
  shadow_context.move(ns);
}

/********************************************************************\

 Function: termination_ctat::unrename_main

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void termination_ctat::unrename_main(const irep_idt &main_backup_id)
{
  // un-rename main
  goto_functionst::function_mapt::iterator main_it=
      temp_goto_functions.function_map.find("main");

  goto_functionst::function_mapt::iterator main_backup_it=
      temp_goto_functions.function_map.find(main_backup_id);

  main_it->second.swap(main_backup_it->second);
}

/********************************************************************\

 Function: termination_ctat::unwinding_init

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void termination_ctat::unwinding_init(  
  const irep_idt &main_backup_id,
  goto_programt::const_targett &loop_begin,
  goto_programt::targett &loop_end,
  goto_programt::const_targett &copy_goto,
  goto_programt::targett &assertion)
{
  rename_main(main_backup_id);

  goto_functionst::function_mapt::iterator main_it=
      temp_goto_functions.function_map.find(ID_main);

  goto_functionst::goto_functiont &main_backup=
      temp_goto_functions.function_map[main_backup_id];

  // get a new main
  main_it->second.body_available=true;
  main_it->second.type=main_backup.type;

  goto_programt::targett t_assertion, t_copy_goto, t_backjump;
  goto_programt &temp=main_it->second.body;
  get_loop_program(loop_begin, loop_end, copy_goto, temp_goto_functions,
                   temp, t_assertion, t_copy_goto, t_backjump);

  assert(t_assertion->type==ASSERT);

  goto_programt::targett eof=--temp.instructions.end();
  assert(eof->is_end_function());

  assert(t_assertion->guard.id()=="=>" &&
         t_assertion->guard.operands().size()==2);

  // we leave the copied_* guard in there, because
  // termination_baset::get_body gets a loop-id from that.
  t_backjump->make_assertion(t_assertion->guard);
  t_backjump->guard.op1()=false_exprt(); // initial RF is false
  t_backjump->targets.clear();
  assertion=t_backjump;

  t_assertion->make_skip(); // kill the original assertion

  t_copy_goto->guard=false_exprt(); // we want the state to get copied!

#if 0
  // Sanity check
  bool found=false;
  forall_goto_program_instructions(it, main_it->second.body)
    if(it==assertion && it->type==ASSERT) found=true;
  assert(found);
#endif
}

/********************************************************************\

 Function: termination_ctat::unwinding_next

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void termination_ctat::unwinding_next(
  goto_programt::const_targett &loop_begin,
  goto_programt::targett &loop_end,
  goto_programt::targett &new_assertion,
  unsigned total_unwindings)
{
  goto_functionst::function_mapt::iterator main_it=
      temp_goto_functions.function_map.find(ID_main);

  assert(main_it!=temp_goto_functions.function_map.end());

  goto_programt &main=main_it->second.body;

  goto_programt::targett eof=--main.instructions.end();
  assert(eof->is_end_function());

  goto_programt::targett assertion=eof; assertion--;
  assert(assertion->is_assert());

  goto_programt::instructiont skip; skip.make_skip();
  main.insert_before_swap(assertion, skip);
  // this assertion contains all the ranking relations!
  new_assertion=++assertion;

  // total_unwindings/2 unwindings are already there!
  for(unsigned i=total_unwindings/2; i<total_unwindings; i++)
  {
    // Get a copy of the loop into temp
    goto_programt temp;

    typedef std::map<goto_programt::const_targett,
                     goto_programt::targett> targets_mappingt;
    targets_mappingt targets_mapping;
    goto_programt::const_targett pend=loop_end; pend++;

    // First get a target mapping
    for(goto_programt::const_targett it=loop_begin; it!=pend; it++)
    {
      goto_programt::targett new_instruction=temp.add_instruction();
      targets_mapping[it]=new_instruction;
      *new_instruction=*it;

      if(new_instruction->is_assert())
      {
        // We don't need that.
        new_instruction->make_skip();
      }
      else if(new_instruction->is_other())
      {
        // Turn declarations into nondet-assignments, just to
        // make sure that locals are re-initialized

        const codet &code=to_code(new_instruction->code);

        if(code.get_statement()=="decl")
        {
          assert(code.operands().size()==1 && code.op0().id()==ID_symbol);

          symbol_exprt se=to_symbol_expr(code.op0());
          side_effect_expr_nondett ne(code.op0().type());
          codet new_code=code_assignt(se, ne);

          new_instruction->make_assignment();
          new_instruction->code=new_code;
        }
      }
    }

    // Update targets
    Forall_goto_program_instructions(it, temp)
    {
      for(goto_programt::targetst::iterator t_it=it->targets.begin();
          t_it!=it->targets.end();
          t_it++)
      {
        targets_mappingt::iterator m_target_it=targets_mapping.find(*t_it);

        if(m_target_it==targets_mapping.end())
        {
          // This must be a loop exit; we thus cut the goto off.
          assert(it->type==GOTO);
          it->targets.clear();
          it->targets.push_back(eof);
          break;
        }

        *t_it=m_target_it->second;
      }
    }

    // add a non-det jump to the assertion.
    goto_programt::targett jump=temp.insert_before(new_assertion);
    jump->make_goto(new_assertion);
    jump->guard = side_effect_expr_nondett(bool_typet());

    // Move the copy over to main
    main.instructions.splice(assertion, temp.instructions);
    main.update();
  }


  // All the backjumps are now assumptions
  Forall_goto_program_instructions(it, main)
  {
    if(it->is_backwards_goto())
    {
      it->type=ASSUME;
      it->targets.clear();
    }
  }
}

/********************************************************************\

 Function: termination_ctat::unwinding_cleanup

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void termination_ctat::unwinding_cleanup(const irep_idt main_backup_id)
{
  unrename_main(main_backup_id);
  temp_goto_functions.function_map.erase(main_backup_id);
}

/********************************************************************\

 Function: termination_ctat::rank_block

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool termination_ctat::rank_block(
  concrete_modelt &model,
  goto_programt::targett &original_assertion,
  goto_programt::targett &original_backjump,
  goto_programt::targett &assertion,
  replace_idt &premap,
  ranking_relation_cachet &ranking_relations,
  const irep_idt &main_backup_id)
{
  assert(assertion->type==ASSERT && assertion->guard.id()==ID_implies);
  goto_tracet goto_trace;

  while(!cegar(model, goto_trace,
               modelchecker_time,
               counter_example_extraction_time,
               ranking_generalization_time))
  {
    paths_analyzed++;

    exprt new_relation=rank_trace(goto_trace, premap);

    if(new_relation.is_false() || new_relation.is_nil())
    {
      if(!exclude_precondition(model, original_assertion,
                               original_backjump, main_backup_id,
                               goto_trace))
      {
        status("Failed to rank a reachable path through the loop.");
        return false;
      }
    }
    else
    {
      if(!ranking_relations.insert(new_relation))
        throw "A ranking function was found a second time!";

      assertion->guard.op1()=ranking_relations.disjunctive_relation();

      std::stringstream msg;      
      msg << "New ranking relation: " << from_expr(new_relation) << std::endl;
      debug(msg.str());
    }
  }

  return true; // ranked!
}

/********************************************************************\

 Function: termination_ctat::exclude_precondition

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool termination_ctat::exclude_precondition(
  concrete_modelt &model,
  goto_programt::targett &assertion,
  goto_programt::targett &backjump,
  const irep_idt &main_backup_id,
  goto_tracet &goto_trace)
{
  if(goto_trace.steps.empty())
    return false;

  if(!cmdline.isset("unranked-method"))
    return false;

  std::string u_method=cmdline.getval("unranked-method");
  if(u_method!="precondition" && u_method!="bmc-precondition")
    return false;

  exprt wp=weakest_precondition(goto_trace);

  // Replace the assertion
  exprt orig_guard=assertion->guard;
  assertion->guard=wp;

  // Kill the backjump, we check a precondition of the loop,
  // not a precondition of the path!
  goto_programt::targett tgt=backjump->targets.front();
  backjump->targets.clear();
  backjump->type=SKIP;

  unrename_main(main_backup_id);

  #if 0
  // sanity check
  forall_goto_functions(it, model.goto_functions)
    forall_goto_program_instructions(iit, it->second.body)
      assert(!iit->is_backwards_goto());
  #endif

  bool res=precondition_is_reachable(wp);
  rename_main(main_backup_id);

  // restore the original program
  backjump->type=GOTO;
  backjump->targets.clear();
  backjump->targets.push_back(tgt);
  assertion->guard=orig_guard;

  if(res)
    return false;
  else
  {
    debug("Precondition is unreachable.");

    // where can we insert unreachable preconditions?
    goto_programt &main=temp_goto_functions.function_map[ID_main].body;
    goto_programt::targett precon_marker=main.instructions.begin();
    while(precon_marker->type==ASSIGN)
    {
      const code_assignt &code=to_code_assign(precon_marker->code);

      if(code.rhs().id()!=ID_sideeffect)
        break;

      const side_effect_exprt &se=to_side_effect_expr(code.rhs());

      if(se.get_statement()!="nondet")
        break;

      precon_marker++;
    }

    goto_programt::targett new_assume=main.insert_before(precon_marker);
    new_assume->make_assumption(not_exprt(wp));
    new_assume->location=precon_marker->location;
    new_assume->function=precon_marker->function;
    main.compute_location_numbers();

    return true;
  }
}

/********************************************************************\

 Function: termination_ctat::rank_trace

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

exprt termination_ctat::rank_trace(
  goto_tracet &goto_trace,
  replace_idt &premap)
{
  if(goto_trace.steps.empty())
  {
    error("Missing counterexample.");
    return false_exprt();
  }

  goto_tracet::stepst::const_iterator begin=goto_trace.steps.begin();
  // skip through the nondet assignments
  while(begin->type==goto_trace_stept::ASSIGNMENT) begin++;

  debug("Found counterexample:");
  show_loop_trace(goto_trace, begin);

  bodyt path_body=termination_baset::get_body(begin, goto_trace);
  replace_nondet_sideeffects(path_body.body_relation);

  if(path_body.body_relation.is_false())
    return false_exprt();

  debug("Synthesising a ranking function for this trace:");
  ranksynth_calls++;
  fine_timet before_ranking=current_time();
  exprt new_relation=ranking(ranking_mode, path_body,
                             context, shadow_context,
                             get_message_handler(),
                             (verbosity>6)?verbosity:2);
  ranking_time+=current_time()-before_ranking;

  // replace any #0-identifiers in the rankfunction
  // with the appropriate pre-symbol.
  premap.replace(new_relation);

  return new_relation;
}

/********************************************************************\

 Function: termination_ctat::all_paths_are_ranked

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool termination_ctat::all_paths_are_ranked(
  concrete_modelt &model,
  goto_tracet &goto_trace)
{
  assert(false);

  return false;

#if 0
  // Execute it
  satcheckt satcheck;
  bv_pointerst bv_pointers(ns, satcheck);
  symex_target_equationt equation(ns);
  goto_symext symex(ns, shadow_context, equation);

  bv_pointers.set_message_handler(get_message_handler());
  bv_pointers.set_verbosity(verbosity);

  symex(goto_functions, temp);
  equation.convert(bv_pointers);

  switch(bv_pointers.dec_solve())
  {
    case decision_proceduret::D_UNSATISFIABLE:
      debug("UNSATISFIABLE, i.e., ranking function ranks all paths.");
      return true;

    case decision_proceduret::D_SATISFIABLE:
    {
      debug("SATISFIABLE, i.e., ranking function does not rank all paths.");
      build_goto_trace(equation, bv_pointers, goto_trace);
      show_goto_trace(std::cout, ns, goto_trace);

//      concrete_counterexamplet ce;
//      build_goto_trace(equation, bv_pointers, ce.goto_trace);
//      show_counterexample(std::cout, context, ce);

      return false;
    }

    default:
      return false;
  }
#endif
}

/********************************************************************\

 Function: termination_ctat::get_loop_program

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void termination_ctat::get_loop_program(
  goto_programt::const_targett &loop_begin,
  goto_programt::targett &loop_end,
  goto_programt::const_targett &copy_goto_src,
  const goto_functionst &goto_functions,
  goto_programt &dest,
  goto_programt::targett &assertion,
  goto_programt::targett &copy_goto_dest,
  goto_programt::targett &backjump)
{
  assert(loop_begin->type==ASSERT);
//  const irep_idt &func=loop_begin->function;
//  goto_functionst::function_mapt::const_iterator fit=
//      goto_functions.function_map.find(func);

//  assert(fit!=goto_functions.function_map.end());
//  const goto_programt &program=fit->second.body;

  dest.clear();

  typedef std::map<goto_programt::const_targett,
                   goto_programt::targett> targets_mappingt;
  targets_mappingt targets_mapping;
  goto_programt::const_targett pend=loop_end; pend++;

  std::set<exprt> symbols;

  for(goto_programt::const_targett it=loop_begin; it!=pend; it++)
  {
    goto_programt::targett new_instruction=dest.add_instruction();
    targets_mapping[it]=new_instruction;
    *new_instruction=*it;

    if(it==copy_goto_src) copy_goto_dest=new_instruction;

    find_symbols(new_instruction->guard, symbols);
    find_symbols(new_instruction->code, symbols);
  }

  goto_programt::targett eof=dest.add_instruction(END_FUNCTION);

  Forall_goto_program_instructions(it, dest)
  {
    for(goto_programt::targetst::iterator t_it=it->targets.begin();
        t_it!=it->targets.end();
        t_it++)
    {
      targets_mappingt::iterator m_target_it=targets_mapping.find(*t_it);

      if(m_target_it==targets_mapping.end())
      {
        // This must be a loop exit; we thus cut the goto off.
        assert(it->type==GOTO);
        it->targets.clear();
        it->targets.push_back(eof);
//        it->make_assumption(not_exprt(it->guard));
        break;
      }

      *t_it=m_target_it->second;
    }
  }

  assert(dest.instructions.size()>1);
  assert(dest.instructions.front().type==ASSERT);
  assertion=dest.instructions.begin();

  backjump=--(--dest.instructions.end());
  assert(backjump->is_backwards_goto());
  assert(copy_goto_dest->type==GOTO);

  if(!backjump->guard.is_true())
  {
    goto_programt::instructiont i;
    i.make_goto(eof, not_exprt(backjump->guard));
    i.function=backjump->function;
    dest.insert_before_swap(backjump, i);
    backjump++;
  }

  dest.update();

  // Add nondet-assignments for all the variables
  for(std::set<exprt>::const_iterator it=symbols.begin();
      it!=symbols.end();
      it++)
  {
    goto_programt::targett t=dest.insert_before(dest.instructions.begin());
    t->make_assignment();

//    if(has_prefix(it->get(ID_identifier).as_string(), "termination::copied"))
//      t->code=code_assignt(*it, false_exprt());
//    else
    t->code=code_assignt(*it, side_effect_expr_nondett(it->type()));
  }

  #if 0
  std::cout << "LOOP PROGRAM: " << std::endl;
  forall_goto_program_instructions(it, dest)
    dest.output_instruction(ns, "", std::cout, it);
  #endif
}

/********************************************************************\

 Function: termination_ctat::operator()

 Inputs:

 Outputs:

 Purpose: "Rank Function First" termination checks

\********************************************************************/

termination_resultt termination_ctat::operator()()
{
  // Precondition: program must be termination-instrumented

  irep_idt main=(cmdline.isset("function"))? cmdline.getval("function") :
                                             "main";
  goto_functionst::function_mapt::const_iterator mit=
      goto_functions.function_map.find(main);

  if(mit==goto_functions.function_map.end() ||
     !mit->second.body_available)
  {
    error("Entry point not found.");
    return T_ERROR;
  }

  if(cmdline.isset("ranksynthesis"))
    ranking_mode=cmdline.getval("ranksynthesis");

  const goto_programt &prog=mit->second.body;
  goto_programt::const_targett entry=prog.instructions.begin();
  std::list<goto_programt::const_targett> recstack;
  std::set<goto_programt::const_targett> seen_loops;

  // this returns a loop multiple times, if it appears on multiple
  // callpaths. There is no need to re-check those, as all callpaths
  // are taken into account by the slicer.
  goto_programt::const_targett assertion=find_next_loop(entry, prog, recstack);
  unsigned i=0;

  while(assertion!=prog.instructions.end())
  {
    if(seen_loops.find(assertion)==seen_loops.end())
    {
      total_loops++;

      const locationt &loc=assertion->location;
      status("==================================================");
      status("Loop Termination Check #" + i2string(total_loops));
      status(std::string("at: ") + ((loc.is_nil()) ? "?" : loc.as_string()));
      status("--------------------------------------------------");

      if(!assertion->guard.is_true())
      {
        i++;
        
        fine_timet time=current_time();
        termination_resultt res=terminates(main, goto_functions, assertion);
        time=current_time()-time;

        status("Check Time: " + time2string(time) + " s");

        if(res!=T_TERMINATING)
        {
          status("LOOP DOES NOT TERMINATE");
          nonterminating_loops++;
        }
        else
          status("LOOP TERMINATES");
      }
      else
      {
        debug("Loop guard simplified by invariant propagation; "
              "loop terminates trivially.");
        status("LOOP TERMINATES");
      }

      status("==================================================");

      seen_loops.insert(assertion);
    }

    assertion = find_next_loop(assertion, prog, recstack);
  }

  assert(recstack.empty());

  if(nonterminating_loops>0)
  {
    status("Program is (possibly) NON-TERMINATING.");
    return T_NONTERMINATING;
  }
  else
  {
    status("Program TERMINATES.");
    return T_TERMINATING;
  }
}

/********************************************************************\

 Function: termination_ctat::weakest_precondition

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

exprt termination_ctat::weakest_precondition(goto_tracet &goto_trace)
{
  debug("Calculating weakest precondition...");

  assert(goto_trace.steps.back().pc->type==ASSERT);

  exprt result=and_exprt(goto_trace.steps.back().pc->guard, false_exprt());

  // we need to skip the nondet-assignmnets in the beginning
  goto_tracet::stepst::const_reverse_iterator end=goto_trace.steps.rend();
  for(end--; end->pc->type==ASSIGN; end--)
  {
    const code_assignt &code=to_code_assign(end->pc->code);

    if(code.rhs().id()!="sideeffect")
      break;

    const side_effect_exprt &se=to_side_effect_expr(code.rhs());
    if(se.get_statement()!="nondet")
      break;
  }
  end++;

  for(goto_tracet::stepst::const_reverse_iterator it=goto_trace.steps.rbegin();
      it!=end;
      it++)
  {
    const goto_programt::const_targett &tgt=it->pc;
    replace_symbolt replace_symbol;

    switch(it->pc->type)
    {
    case ASSUME:
    case GOTO:
      {
        exprt guard=it->cond_expr;

        if(!guard.is_nil())
        {
          remove_ssa_ids(guard);
          if(!it->cond_value) guard.make_not();

//          std::cout << "GOTO/ASSUME: " << from_expr(ns, "", guard) << std::endl;

          result=implies_exprt(guard, result);
          simplify(result, ns);
        }
      }
      break;

    case OTHER:
    case ASSIGN:
      {
        symex_target_equationt equation(ns);
        codet tmp_code=to_code(tgt->code);

//        std::cout << "ASSIGN: " << from_expr(ns, "", tmp_code)<< std::endl;

        exprt predicate_wp=wp(tmp_code, result, ns);

        simplify(predicate_wp, ns);
        result=predicate_wp;
      }
      break;

    default:
      // ignore
      break;
    }

//    std::cout << "NOW: " << from_expr(ns, "", result) << std::endl;
  }

  result.make_not(); // We need that because we started from false (?)
  simplify(result, ns);

  return result;
}

/********************************************************************\

 Function: termination_ctat::show_stats

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void termination_ctat::show_stats(void)
{
  std::stringstream ss("");

  ss << "RF Generalization: " <<
    time2string(ranking_generalization_time) << " s total.";

  status(ss.str());
  termination_path_enumerationt::show_stats();
}

