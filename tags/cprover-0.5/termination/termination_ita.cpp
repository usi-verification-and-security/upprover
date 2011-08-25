/*******************************************************************\

Module: 

Author: CM Wintersteiger

\*******************************************************************/

#include <util/replace_symbol.h>
#include <util/prefix.h>
#include <util/simplify_expr.h>

#include <ivt/wolver.h>

#include <goto-programs/write_goto_binary.h>
#include <goto-programs/remove_unused_functions.h>

#include "termination_ita.h"

/********************************************************************\

 Function: termination_itat::operator()

 Inputs:

 Outputs:

 Purpose: 

\********************************************************************/

termination_resultt termination_itat::operator()()
{
  return termination_ctat::operator()();
}

/********************************************************************\

 Function: termination_itat::show_stats

 Inputs:

 Outputs:

 Purpose: 

\********************************************************************/

void termination_itat::show_stats(void)
{
  termination_ctat::show_stats();
}

/********************************************************************\

 Function: termination_itat::copy

 Inputs:

 Outputs:

 Purpose: 

\********************************************************************/

void termination_itat::copy(
  goto_programt::const_targett &loop_begin,
  goto_programt::targett &loop_end,
  goto_programt::const_targett &copy_goto,
  goto_programt &dest) const
{   
  // Definitions for mapping between the two programs
  typedef std::map<goto_programt::const_targett,
                   goto_programt::targett> targets_mappingt;
  targets_mappingt targets_mapping;

  // Loop over program - 1st time collects targets and copy

  goto_programt::const_targett onemore = loop_end; onemore++;
  for(goto_programt::const_targett it=loop_begin; it!=onemore; it++)
  {    
    goto_programt::targett new_instruction=dest.add_instruction();
    targets_mapping[it]=new_instruction;
    *new_instruction=*it;
    if (new_instruction->type==ASSERT)
      new_instruction->make_skip(); 
    else if (it==copy_goto)
      new_instruction->make_skip(); // we want to copy the state!
  }

  // Loop over program - 2nd time updates goto targets

  for(goto_programt::targett it=targets_mapping[loop_begin];
      it!=targets_mapping[loop_end];
      it++)
  {
    for(goto_programt::instructiont::targetst::iterator
          t_it=it->targets.begin();
        t_it!=it->targets.end();
        t_it++)
    {
      targets_mappingt::iterator
        m_target_it=targets_mapping.find(*t_it);
      
      if(m_target_it==targets_mapping.end())
      {
        // This is a loop exit; we just cut that path off. 
        it->guard.make_false();
        it->type = ASSUME;
        it->labels.push_back("exit path cut off");
        it->targets.clear();
        break;
      }
      else
        *t_it=m_target_it->second;
    }
  }  
  
  // Last instruction is now a backjump, we turn that into an assumption.
  goto_programt::targett last=--dest.instructions.end();
  assert(last->type==GOTO);  
  last->type=ASSUME;
  last->targets.clear();
}

/********************************************************************\

 Function: termination_itat::make_compositional

 Inputs:

 Outputs:

 Purpose: 

\********************************************************************/

bool termination_itat::make_compositional(
    goto_programt::const_targett &loop_begin,
    goto_programt::targett &loop_end,
    goto_programt::const_targett &loop_copy_goto,
    goto_programt::targett &loop_assertion,
    concrete_modelt &model,
    replace_idt &premap,
    ranking_relation_cachet &ranking_relations)
{
  status("Ranking argument is not compositional; "
         "strengthening via interpolation.");
  
  // Precondition: program is loop-free between begin and end.
  // Want: L(x, x') ; L(x', x'') & -T(x, x'')
  
  goto_programt temp;
  exprt rr=ranking_relations.disjunctive_relation();
  
  std::set<exprt> syms;  
  find_symbols(rr, syms);
  replace_symbolt old_syms;
  replace_symbolt old_syms_rev;
  
  for(std::set<exprt>::const_iterator it=syms.begin(); it!=syms.end(); it++)
  {
    irep_idt name = it->get(ID_identifier);
    
    if (!has_prefix(name.as_string(), "termination::pre::"))
    {
      temp.add_instruction(ASSIGN);    
      temp.instructions.back().code=
          code_assignt(*it, side_effect_expr_nondett(it->type()));
      
      // introduce an old_sym that we can reference later on
      symbolt old_sym = ns.lookup(it->get(ID_identifier));
      symbolt new_sym = old_sym;
      new_sym.name = "ITA_SAVED::" + new_sym.name.as_string();
      new_sym.base_name = old_sym.base_name.as_string() + "''";
      new_sym.pretty_name = old_sym.pretty_name.as_string() + "''";
      exprt new_sym_expr = symbol_exprt(new_sym.name, new_sym.type);
      temp.add_instruction(ASSIGN);
      temp.instructions.back().code = code_assignt(new_sym_expr, *it);
      shadow_context.move(new_sym);
    }
    else // does have the prefix
    {
      std::string n=name.as_string(); // strip the pre-prefix
      n = n.substr(n.find("::") + 2);
      n = n.substr(n.find("::") + 2);
      n = n.substr(n.find("::") + 2);
      irep_idt real_name = "ITA_SAVED::" + n;
      
      old_syms.insert(name, symbol_exprt(real_name, it->type()));
      old_syms_rev.insert(real_name, symbol_exprt(name, it->type()));
    }
  }
  
  // rr_replace = T with all `old' symbols replaced by the 
  // `really old' ones with the "ITA_SAVED" prefix 
  exprt rr_replaced=rr;
  old_syms.replace(rr_replaced);
      
  copy(loop_begin, loop_end, loop_copy_goto, temp);  
  //temp.add_instruction(ASSUME);
  //temp.instructions.back().guard=rr;
  
  // This is where we want the interpolant.
  goto_programt::const_targett partition_point=--temp.instructions.end();
    
  copy(loop_begin, loop_end, loop_copy_goto, temp);
//  temp.add_instruction(ASSUME);
//  temp.instructions.back().guard=rr;    
    
  temp.add_instruction(ASSERT);  
  temp.instructions.back().guard=rr_replaced;
  
  temp.add_instruction(END_FUNCTION);
  temp.update();
  

#if 1
  // save the temporary program
  goto_functionst gf;
  contextt ctx = context;
  
  gf.copy_from(goto_functions);  
  irep_idt name=ID_main; // overwrite main
  gf.function_map[name].body.clear();
  gf.function_map[name].body.copy_from(temp);
  gf.function_map[name].body_available=true;
  
  for(contextt::symbolst::const_iterator it=shadow_context.symbols.begin();
      it!=shadow_context.symbols.end();
      it++)
    ctx.add(it->second);
  
  remove_unused_functions(gf, *message_handler);
  write_goto_binary("inter.gbf", ctx, gf, *message_handler);
#endif
  

  if (verbosity>=9)
    temp.output(ns, "", std::cout);
    

  goto_tracet error_trace;
  // need new context with both
  contextt temp_context;
  forall_symbols(it, context.symbols) temp_context.add(it->second);
  forall_symbols(it, shadow_context.symbols) temp_context.add(it->second);
  wolvert wolver(temp_context, temp_goto_functions, error_trace, get_message_handler());
  wolver.options.set_option("interpolator", "princess");
  if (verbosity>=9) wolver.options.set_option("show-invariants", true);
  
  temp_goto_functions.function_map[ID_main].body.swap(temp);
  bool res = wolver.fight();
  temp_goto_functions.function_map[ID_main].body.swap(temp);

  if (!res)
  {
    status("Wolver said SAFE.");

    // Get the interpolant.  
    exprt inv = wolver.get_invariant(partition_point);
    old_syms_rev.replace(inv);
    std::cout << "INVARIANT (at " << partition_point->location_number<< "): " 
        << from_expr(ns, "", inv) << std::endl;
    
    ranking_relations.add_constraint(inv);
    if (ranking_relations.is_compositional())
      return true;
  }
  else
    status("Wolver said UNSAFE.");
  
  
  status("Strengthening failed.");
  return false;
}
