/*******************************************************************\

Module: Termination module: the path enumeration method 

Author: CM Wintersteiger

\*******************************************************************/

#include <limits.h>
#include <sstream>
#include <fstream>
#include <memory>

#include <std_expr.h>
#include <i2string.h>
#include <prefix.h>
#include <replace_symbol.h>
#include <simplify_expr.h>
#include <decision_procedure.h>

#include <pointer-analysis/value_set_analysis.h>
#include <pointer-analysis/goto_program_dereference.h>

#include <goto-programs/invariant_propagation.h>
#include <goto-programs/goto_inline_class.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/wp.h>

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>

#include <goto-symex/goto_symex_state.h>
#include <goto-symex/basic_symex.h>

#include "termination_path_enumeration.h"
#include "termination_slicer.h"
#include "ranking.h"
#include "find_symbols_rw.h"
#include "replace_identifier.h"

/********************************************************************\

 Function: termination_path_enumerationt::terminates

 Inputs:

 Outputs:

 Purpose: Perform Termination Check for one specific loop

\********************************************************************/

termination_resultt termination_path_enumerationt::terminates(
  const irep_idt &main,
  const goto_functionst &goto_functions,
  goto_programt::const_targett assertion)
{  
  if(!get_model(main, goto_functions, assertion))
  {
    status("Slicer has shown unreachability of the assertion.");
    return T_TERMINATING;
  }
    
  goto_programt::const_targett loop_end, loop_begin, copy_goto;    
  get_loop_extent(sliced_assertion, loop_begin, loop_end, copy_goto);

  // We don't care if the loop is reachable right now.
  
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
    const goto_programt &prog=sliced_goto_functions.function_map[function].body;
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
  
  if(rank(loop_begin, loop_end, copy_goto, premap, 
          ranking_relations)==T_NONTERMINATING)
  {
    if(u_mode=="none" || u_mode=="precondition" || u_mode=="bmc-precondition") 
      return T_NONTERMINATING;
    else
    {
      if(u_mode!="cegar" && u_mode!="bmc")
        throw "Unknown unranked-method";
      
      // The loop is non-terminating, and we don't know about the preconditions.
      // We need to check if this is reachable.
      
      if(is_reachable(loop_begin, loop_end, u_mode=="bmc"))
        return T_NONTERMINATING;
      else
      {
        status("Loop is potentially non-terminating, but unreachable.");
        return T_TERMINATING;
      }
    }
  }
  else
    return check_rank_relations(ranking_relations);
}

/********************************************************************\

 Function: termination_path_enumerationt::get_model

 Inputs:

 Outputs:

 Purpose: 

\********************************************************************/

bool termination_path_enumerationt::get_model(
  const irep_idt &main,
  const goto_functionst &goto_functions,
  goto_programt::const_targett assertion)
{  
  fine_timet before=current_time();
  
  bool mres=sliced_abstraction(context,
                               shadow_context,
                               goto_functions,
                               main,
                               assertion,
                               sliced_assertion,
                               sliced_goto_functions,
                               get_message_handler(),
                               false, /* no self-loops */
                               true, /* kill loops */
                               (unsigned)-1, /* dep. limit */
                               true /* replace malloc */ );
  
  slicing_time+=current_time()-before;
  
  if(!mres) 
    return false;
  
  #if 0
  std::ofstream f("model");
  goto_functions.output(ns, f);
  f.close();
      
  f.open("sliced_model");
  dest_func.output(ns, f);
  f.close();
  #endif
  
  assert(sliced_assertion->type==ASSERT);
  
  const irep_idt &func=sliced_assertion->function;
  assert(func!="");
  goto_programt &program=sliced_goto_functions.function_map[func].body;

  // Search for the backjump
  goto_programt::targett bj=sliced_assertion;
  while(!bj->is_backwards_goto() &&
        bj!=program.instructions.end()) bj++;
  
  if(bj==program.instructions.end())
    return false; // This must be a one-shot loop.
  
  if(!is_local(sliced_assertion, bj))
  {
    status("Inlining loop because termination may be "
           "influenced by global variables...");

    goto_inlinet gi(sliced_goto_functions, ns, get_message_handler());    
    
    for(goto_programt::targett it=sliced_assertion;
        it!=bj;
        /* Nothing */ )
    {
      gi.inline_instruction(program, true, it);
    }
          
    program.update();
  }

  /*
  if(cmdline.isset("no-value-sets"))
    sliced_model.value_set_analysis.initialize(sliced_model.goto_functions);
  else
  {
    status("Pointer analysis...");  
    fine_timet before=current_time();
    sliced_model.value_set_analysis(sliced_model.goto_functions);  
    pointer_analysis_time=current_time()-before;
  }
  */
      
//  // Remove pointers
//  goto_program_dereferencet gpd(ns, shadow_context, optionst(),
//                                sliced_model.value_set_analysis);
//  gpd.dereference_program(sliced_model.goto_functions, false);
  
  return true;
}

/********************************************************************\

 Function: termination_path_enumerationt::rank_pathwise

 Inputs:

 Outputs:

 Purpose: 

\********************************************************************/

termination_resultt termination_path_enumerationt::rank(
  goto_programt::const_targett &loop_begin,
  goto_programt::const_targett &loop_end,
  goto_programt::const_targett &copy_goto,
  replace_idt &premap,
  ranking_relation_cachet &ranking_relations)
{
  status("Generating ranking functions...");
  
  bodyt path_body;
  path_mapt path_map;
  initialize_paths(loop_begin, loop_end, path_map);
    
  do // while get_next_path
  {
    paths_analyzed++;
    
    #if 0
    std::cout << "PATH MAP: ";
    for(path_mapt::const_iterator it=path_map.begin();
        it!=path_map.end();
        it++)
      std::cout << ((it->second)?"1":"0");
    std::cout << std::endl;
    #endif
    
    // We don't want any paths that don't copy their state.
    path_mapt::const_iterator pit=path_map.find(copy_goto);
    if(pit!=path_map.end() && pit->second) continue;
    
    path_body=extract_path(loop_begin, loop_end, path_map);
    replace_nondet_sideeffects(path_body.body_relation);

    #if 0
    std::cout << "PATH: " << from_expr(ns, "", path_body.body_relation) << 
      std::endl;
    
    if(!path_body.body_relation.is_false())
    {
      std::cout << "Variable Map: " << std::endl;
      for(bodyt::variable_mapt::const_iterator vit=path_body.variable_map.begin();
          vit!=path_body.variable_map.end();
          vit++)
        std::cout << "  " << vit->first << " -> " << vit->second << std::endl;
    }
    #endif
    
    if(!is_feasible(path_body))
    {
      paths_infeasible++;      
      continue;
    }
    
    fine_timet before=current_time();
    bool is_ranked=ranking_relations.is_ranked(path_body.body_relation);
    ranking_cache_time+=current_time()-before;
        
    if(is_ranked)
    {
      debug("Ranking relation cache hit.");
      continue; // we already have a ranking function for this path
    }
    
    ranksynth_calls++;
    fine_timet before_ranking=current_time();    
    exprt new_relation=ranking(ranking_mode, path_body, 
                               context, shadow_context, 
                               get_message_handler(),
                               (verbosity>6)?verbosity:2);
    ranking_time+=current_time()-before_ranking;
    
    
    if(new_relation.is_false() || new_relation.is_nil())
    {
      // couldn't find a rank function.
      value_set_analysist va(ns);
      exprt wp=weakest_precondition(loop_begin, loop_end, copy_goto,
                                    path_map, va);
        
      if(precondition_is_reachable(wp))
        return T_NONTERMINATING;
      else
      {
        debug("Precondition is unreachable.");
        // No fixing needed, path will not be enumerated again
        // unreachable_preconditions.insert(wp);
      }        
    }
    else
    {    
      // replace any #0-identifiers in the rankfunction 
      // with the appropriate pre-symbol.    
      premap.replace(new_relation);
      ranking_relations.insert(new_relation);
      
      #if 0
      std::cout << "RANKING RELATION: " << from_expr(new_relation) << 
        std::endl;
      #endif
    }
  
  } while(get_next_path(path_map)) ;
  
  return T_UNKNOWN;
}


/********************************************************************\

 Function: termination_path_enumerationt::precondition_is_reachable

 Inputs:

 Outputs:

 Purpose: 

\********************************************************************/

bool termination_path_enumerationt::precondition_is_reachable(
    const exprt &precondition)
{
  if(precondition.is_false()) return false;
  
  if(!cmdline.isset("unranked-method"))
    return false;
  
  std::string u_method=cmdline.getval("unranked-method");
  if(u_method!="precondition" && u_method!="bmc-precondition")
    return false;
  
  // This checks the precondition in the original (sliced) model 
  // i.e., this _does_ contain the backjump if it was not removed before.
  
  exprt old_guard=sliced_assertion->guard; // safe this
  
  debug("Precondition: " + from_expr(ns, "", precondition));
  sliced_assertion->guard=not_exprt(precondition);
  
  #if 0
  std::ofstream out("precondition_model");
  model.goto_functions.output(ns, out);
  out.close();
  #endif
  
  bool res;
  
  if(u_method=="bmc-precondition")
  {
    status("Running BMC precondition check...");
    concrete_modelt model(ns, sliced_goto_functions);
    res=!bmc(model, modelchecker_time,
             wp_ce_extraction_time, wp_unreachability_time);
  }
  else
  {
    status("Running CEGAR precondition check...");
    concrete_modelt model(ns, sliced_goto_functions);
    res=!cegar(model, modelchecker_time, 
               wp_ce_extraction_time, wp_unreachability_time);
  }
  
  // restore the old guard.
  sliced_assertion->guard=old_guard;
  
  return res;
}

/********************************************************************\

 Function: termination_path_enumerationt::check_rank_relations

 Inputs:

 Outputs:

 Purpose: 

\********************************************************************/

termination_resultt termination_path_enumerationt::check_rank_relations(  
  ranking_relation_cachet &ranking_relations)
{
  if(ranking_relations.size()==0)
  {
    debug("Suspicious: All paths are infeasible.");
    return T_TERMINATING;
  }
  
  // Are those ranking functions enough to prove termination?
  status("Synthesized " + i2string(ranking_relations.size()) + 
         " ranking functions.");
  
  switch(ranking_relations.size())
  {
    case 0:
      // No ranking functions, i.e., preconditions of all paths
      // have been proven unreachable before. 
      return T_TERMINATING;
      
    case 1:
      // The same ranking function works on all paths. 
      // No combination of paths could possibly violate it.    
      return T_TERMINATING;
    
    default:
      assert(sliced_assertion->guard.id()=="=>");
      sliced_assertion->guard.op1()=ranking_relations.disjunctive_relation();
              
      concrete_modelt model(ns, sliced_goto_functions);
      return bre_loop(model);
  }
}

/********************************************************************\

 Function: termination_path_enumerationt::get_pre_post_mapping

 Inputs:

 Outputs:

 Purpose: 

\********************************************************************/

void termination_path_enumerationt::get_pre_post_mapping(
  goto_programt::const_targett &loop_begin,
  goto_programt::const_targett &loop_end,
  replace_idt &premap) const
{
  // We read the mapping off of the program. This requires 
  // the state-saving instrumentation.
  
  for(goto_programt::const_targett it=loop_begin; it!=loop_end; it++)
  {
    if(it->is_assign())
    {
      const code_assignt &code=to_code_assign(it->code);
      if(code.lhs().id()==ID_symbol && 
         code.rhs().id()==ID_symbol &&
         has_prefix(code.lhs().get(ID_identifier).as_string(), 
                    termination_prefix))
      {
        irep_idt badid=code.rhs().get(ID_identifier).as_string() + "#0";       
        premap.insert(badid, code.lhs().get(ID_identifier));
      }
    }
  }
}

/********************************************************************\

 Function: termination_path_enumerationt::is_feasible

 Inputs:

 Outputs:

 Purpose: 

\********************************************************************/

bool termination_path_enumerationt::is_feasible(bodyt &body)
{
  if(body.body_relation.is_false()) return false;
  
  fine_timet before=current_time();
  satcheckt solver;
  bv_pointerst converter(ns, solver);   
  
  solver.set_message_handler(get_message_handler());
  converter.set_message_handler(get_message_handler());
  solver.set_verbosity(2);
  converter.set_verbosity(2);
  
  converter.set_to_true(body.body_relation);
  
  satcheckt::resultt res=solver.prop_solve();

  path_feasibility_time+=current_time()-before;
  
  if(res==satcheckt::P_UNSATISFIABLE)
    return false;
  
  return true;
}

/********************************************************************\

 Function: termination_path_enumerationt::is_reachable

 Inputs:

 Outputs:

 Purpose: 

\********************************************************************/

bool termination_path_enumerationt::is_reachable(
  goto_programt::const_targett &loop_begin, 
  goto_programt::const_targett &loop_end,
  bool use_bmc)
{
  bool res=true;
  exprt orig_guard=sliced_assertion->guard;  
  
  // Adjust assertion, remove loop
  sliced_assertion->guard=false_exprt();
  
  goto_programt::targett it=sliced_assertion;
  while(!it->is_backwards_goto()) it++;
  
  goto_programt::targett tgt=it->targets.front();  
  it->targets.clear();
  it->type=SKIP;
  
  status("Checking loop reachability...");
    
  #if 0 
//  it->labels.push_back("KILLED_GOTO");
//  std::ofstream f("model");
//  model.goto_functions.output(ns, f);
//  f.close();
    
  // sanity check
  forall_goto_functions(fit, model.goto_functions)
    forall_goto_program_instructions(iit, fit->second.body)
      if(iit->is_backwards_goto())
      {
        debug("Unexpected backjump in program.");        
        it->type=GOTO;
        it->targets.clear();
        it->targets.push_back(tgt);
        assertion->guard=orig_guard;
        return true;
      }
  #endif  
  
  #if 0
  std::cout << "CHECK PROGRAM: " << std::endl;
  model.goto_functions.output(ns, std::cout);
  #endif
  
  if(use_bmc)
  {
    concrete_modelt model(ns, sliced_goto_functions);
    res=!bmc(model, modelchecker_time, 
             loop_reachability_time, loop_reachability_time);
  }
  else
  {
    concrete_modelt model(ns, sliced_goto_functions);
    res=!cegar(model, modelchecker_time, 
               loop_reachability_time, loop_reachability_time);    
  }
  
  // restore the original program
  it->type=GOTO;
  it->targets.clear();
  it->targets.push_back(tgt);
  sliced_assertion->guard=orig_guard;
  
  return res;
}

/********************************************************************\

 Function: termination_path_enumerationt::weakest_precondition

 Inputs:

 Outputs:

 Purpose: 

\********************************************************************/

exprt termination_path_enumerationt::weakest_precondition(
  goto_programt::const_targett &loop_begin,
  goto_programt::const_targett &loop_end,
  goto_programt::const_targett &copy_goto,
  const path_mapt &path_map,
  value_setst &va)
{
//  debug("Calculating weakest precondition...");
  assert(loop_end->is_backwards_goto());
  
  // first get a `trace'
  typedef std::list<std::pair<goto_programt::const_targett, bool> > tracet;
  tracet trace;
  
  for(goto_programt::const_targett it=loop_begin;
      it!=loop_end;
      /* no increment */)
  {
    goto_programt::const_targett next=it; next++;
    
    if(it==copy_goto) 
    {
      // we skip this one, as we're interested in both paths; 
      // the one that copies and the one that doesn't
      it++; 
      continue; 
    }
    
    switch(it->type)
    {
      case ASSIGN:
        trace.push_back(std::make_pair(it, true));        
        break;
      case ASSUME:
        trace.push_back(std::make_pair(it, true));
        break;
      case GOTO:
      {
        path_mapt::const_iterator pit=path_map.find(it);
        assert(pit!=path_map.end());
        
        if(it->guard.is_true())
          next=it->targets.front();
        else if(it->guard.is_false())
          assert(!pit->second);
        else
        {
          if(pit->second)
            next=it->targets.front();
          
          trace.push_back(std::make_pair(it, pit->second));
        }
        break;
      }
      case ASSERT: /* ignored. (treat as assume?) */
      default:
        /* ignore */ ;
    }

    it=next;
  }
  
  
  exprt result=and_exprt(loop_end->guard, false_exprt());
  
  for(tracet::reverse_iterator rit=trace.rbegin();
      rit!=trace.rend();
      rit++)
  {
    const goto_programt::const_targett &tgt=rit->first;
    replace_symbolt replace_symbol;
    
    switch(tgt->type)    
    {
      case OTHER:
      case ASSIGN:
      {
        symex_target_equationt equation(ns);
        codet tmp_code=to_code(tgt->code);
        
        #if 0
        std::cout << "ASSIGN:" << from_expr(ns, "", tmp_code) << std::endl;
        #endif
        
        exprt predicate_wp=wp(tmp_code, result, ns);
        simplify(predicate_wp, ns);
        result=predicate_wp;
        
        break;
      }
      case GOTO:
      case ASSUME:
      {
        exprt guard=tgt->guard;
        result = implies_exprt((rit->second) ? guard : not_exprt(guard),
                               result);
        break;
      }
      default:
        throw "Unhandled instruction type.";
    }
    
    #if 0
    std::cout << "PRECON NOW: " << from_expr(ns, "", result) << std::endl;
    #endif
  }
  
  result.make_not(); // We need that because we started from false (?)
  simplify(result, ns);
  
  return result;
}

/********************************************************************\

 Function: termination_path_enumerationt::extract_path

 Inputs:

 Outputs:

 Purpose: 

\********************************************************************/

bodyt termination_path_enumerationt::extract_path(
  goto_programt::const_targett &loop_begin,
  goto_programt::const_targett &loop_end,
  const path_mapt &path_map)
{
  bodyt result;
  exprt::operandst op;
  
  std::map<irep_idt, unsigned> ssa_counters;
  replace_mapt constants;
  replace_idt replace_id;  
  
  
  for(goto_programt::const_targett it=loop_begin;
      it!=loop_end;
      /* no increment */)
  {
    goto_programt::const_targett next=it; next++;
    
    switch(it->type)
    {
      case ASSIGN:
      {
        code_assignt code=to_code_assign(it->code);
        
        find_symbols_sett w;
        find_symbols_w(code.lhs(), w);
        
        equality_exprt equality(code.lhs(), code.rhs());        
        replace_id.replace(equality.rhs());
        
        // All the written ones get their SSA-ID updated
        for(find_symbols_sett::const_iterator it=w.begin();
            it!=w.end();
            it++)
        {
          // Are we writing a pre-variable?
          if(has_prefix(it->as_string(), termination_prefix))
          {
            assert(code.rhs().id()=="symbol");
            const irep_idt &post_id=code.rhs().get("identifier");
            const irep_idt &pre_id=code.lhs().get("identifier");
            result.variable_map[post_id]=pre_id;            
            
            // the RHS gets a #0 id
            irep_idt new_id=post_id.as_string()+"#0";
            replace_id.insert(post_id, new_id);
            equality.rhs().set("identifier", new_id);
          }
          else
          {
            const irep_idt &old_id=*it;
            unsigned cur=++ssa_counters[old_id]; // 0 is never used
            
            // gets a new ID            
            irep_idt new_id=old_id.as_string()+"#"+i2string(cur);
            replace_id.insert(old_id, new_id);
          }
        }
                
        replace_id.replace(equality.lhs());                
        
        if(equality.rhs().is_constant())
          constants[equality.lhs()]=equality.rhs();
        
        replace_expr(constants, equality);
        
        op.push_back(equality);
        break;
      }
      case ASSUME:
      {
        if(it->guard.is_false())
        {
          // This path is infeasible. 
          result.body_relation=false_exprt();
          result.variable_map.clear();
          return result;
        }
        
        if(!it->guard.is_true())
        {
          exprt guard=it->guard;
          
          find_symbols_sett syms;
          find_symbols(guard, syms);
                    
          for(find_symbols_sett::const_iterator it=syms.begin();
              it!=syms.end();
              it++)
          {
            if(ssa_counters.find(*it)==ssa_counters.end())
              ssa_counters[*it]=0;
          }
          
          replace_id.replace(guard);
          replace_expr(constants, guard);
          op.push_back(guard);
        }
        break;
      }
      case GOTO:
      {
        path_mapt::const_iterator pit=path_map.find(it);
        assert(pit!=path_map.end());
        
        if(it->guard.is_true())
        {
          assert(pit->second);
          next=it->targets.front();
        }
        else if(it->guard.is_false())
        {
          assert(!pit->second);
          /* next is okay */
        }
        else
        {
          exprt guard=it->guard;
          ssa_replace(guard, replace_id, ssa_counters);
          
          if(pit->second)
            next=it->targets.front();
          else
            guard.make_not();
          
          replace_expr(constants, guard);
          op.push_back(guard);
        }
        break;
      }
      case FUNCTION_CALL: /* IGNORED! */ 
        break; 
      case OTHER:
      {
        const irep_idt &stmt=it->code.get("statement");
        
        if(stmt=="decl")
          /* ignore */ ;
        else if(stmt=="expression")
          /* those are side-effect-free, aren't they? */ ;
        else
          throw "Unknown `other' instruction: " + stmt.as_string();

        break;
      }
      case ASSERT: /* ignored. (treat as assume?) */ break;
      default:
        /* ignore */ ;
    }
    
    if(next->location_number > loop_end->location_number)
    {
      // this is a loop exit
      result.body_relation=false_exprt();
      result.variable_map.clear();
      return result;
    }
    
    it=next;
  }  
  
  // just in case the backjump is conditional.
  if(!loop_end->guard.is_true())
  {
    assert(!loop_end->guard.is_false());    
    exprt guard=loop_end->guard;
    ssa_replace(guard, replace_id, ssa_counters);
    replace_expr(constants, guard);
    op.push_back(guard);
  }
  
  replace_idt vri;
  
  // set up the variable map; this must be in terms of actual
  // program variables (e.g., c::x and c::x')
  for(std::map<irep_idt, unsigned>::const_iterator sit=ssa_counters.begin();
      sit!=ssa_counters.end();
      sit++)
  {
    if(sit->second==0) continue;
    
    irep_idt id=sit->first;
    irep_idt pre_id=id.as_string()+"#"+i2string(0);
    
    const symbolt &symbol=ns.lookup(id);            
    
    for(unsigned i=0; i<sit->second; i++)
    {
      symbolt newsym;
      newsym.name=id.as_string()+"#"+i2string(i);
      newsym.base_name=newsym.name;
      newsym.type=symbol.type;
      
      shadow_context.move(newsym); // we don't care if it's already there.
    }
    
    vri.insert(id.as_string()+"#"+i2string(sit->second), id);    
    
    result.variable_map[id]=pre_id;
  }
      
  result.body_relation=and_exprt(op);
  vri.replace(result.body_relation);  
  
  return result;
}

/********************************************************************\

 Function: termination_path_enumerationt::is_local

 Inputs:

 Outputs:

 Purpose: 

\********************************************************************/

bool termination_path_enumerationt::is_local(
  goto_programt::targett loop_begin,
  goto_programt::targett loop_end)
{
  find_symbols_sett symbols;
  goto_programt::targett stop=loop_end; stop++;
  
  for(goto_programt::targett it=loop_begin;
      it!=stop;
      it++)
  {
    switch(it->type)
    {
      case ASSIGN:
      {
        const code_assignt &code=to_code_assign(it->code);
        
        if(!(code.lhs().id()=="symbol" && // ignore state-saving
             has_prefix(code.lhs().get("identifier").as_string(), 
                        termination_prefix)))
          find_symbols(code.rhs(), symbols);
        break;
      }
      case ASSUME:
      case GOTO:
      {
        const exprt &guard=it->guard;
        find_symbols(guard, symbols);
        break;
      }
      default:
        /* ignore */ ;
    }
  }
  
  for(find_symbols_sett::const_iterator it=symbols.begin();
      it!=symbols.end();
      it++)
  {
    const symbolt *sp;    
    ns.lookup(*it, sp);
    
    if(sp->static_lifetime)
      return false;
  }
  
  return true;
}

/********************************************************************\

 Function: termination_path_enumerationt::ssa_replace

 Inputs:

 Outputs:

 Purpose: 

\********************************************************************/

void termination_path_enumerationt::ssa_replace(
  exprt &expr, 
  replace_idt &replace_id,
  std::map<irep_idt, unsigned> &ssa_counters) const
{
  find_symbols_sett syms;
  find_symbols(expr, syms);
            
  // find new, uncounted symbols
  for(find_symbols_sett::const_iterator sit=syms.begin();
      sit!=syms.end();
      sit++)
  {
    if(ssa_counters.find(*sit)==ssa_counters.end())
    {              
      ssa_counters[*sit]=0;
      irep_idt new_id=sit->as_string()+"#"+i2string(0);
      replace_id.insert(*sit, new_id);
    }
  }
  
  replace_id.replace(expr);
}

/********************************************************************\

 Function: termination_path_enumerationt::get_loop_extent

 Inputs:

 Outputs:

 Purpose: 

\********************************************************************/

void termination_path_enumerationt::get_loop_extent(
  goto_programt::targett &assertion,
  goto_programt::const_targett &begin,
  goto_programt::const_targett &end,
  goto_programt::const_targett &copy_goto)
{  
  assert(assertion->type==ASSERT);
  copy_goto=assertion;
  
  goto_programt::targett it=assertion;
  while(!it->is_backwards_goto() || it->targets.front()==it) 
  {
    if(it->is_goto() && it->guard.id()=="or" &&
       it->guard.operands().size()==2 &&
       it->guard.op0().id()=="symbol" &&
       has_prefix(it->guard.op0().get("identifier").as_string(), 
                  "termination::copied"))
      copy_goto=it;
    
    it++;   
  }
  
  assert(copy_goto->type==GOTO);  
  assert(it->targets.size()==1);
     
  end=it;
  begin=it->targets.front();  
}

/********************************************************************\

 Function: termination_path_enumerationt::initialize_paths

 Inputs:

 Outputs:

 Purpose: gets the next path

\********************************************************************/

void termination_path_enumerationt::initialize_paths(
  goto_programt::const_targett &begin,
  goto_programt::const_targett &end,
  path_mapt &path_map)
{
  path_map.clear();
  
  goto_programt::const_targett it=begin;
  while(it!=end)
  {
    if(it->is_goto())
      path_map[it]=it->guard.is_true() ? true : false;
    
    it++;
  }
  
  assert(end->is_goto());
  path_map[end]=true;
}

/********************************************************************\

 Function: termination_path_enumerationt::get_next_path

 Inputs:

 Outputs:

 Purpose: gets the next path

\********************************************************************/

bool termination_path_enumerationt::get_next_path(path_mapt &path_map) const
{
  for(path_mapt::reverse_iterator it=path_map.rbegin();
      it!=path_map.rend();
      it++)
  {
    if(it->second)
    {
      if(!it->first->guard.is_true())
        it->second=false;
    }
    else if(!it->first->guard.is_false())
    {
      it->second=true;
      return true;
    }
  }
  
  return false;
}

/********************************************************************\

 Function: termination_path_enumerationt::path_string

 Inputs:

 Outputs:

 Purpose: 

\********************************************************************/

std::string termination_path_enumerationt::path_string(const path_mapt &path_map) const
{
  std::string res("");
  
  for(path_mapt::const_iterator pit=path_map.begin();
      pit!=path_map.end();
      pit++)
    if(pit->second) res+="1"; else res+="0";  
  
  return res;
}

/********************************************************************\

 Function: termination_path_enumerationt::show_stats()

 Inputs:

 Outputs:

 Purpose:  

\********************************************************************/

void termination_path_enumerationt::show_stats(void)
{
  std::stringstream ss;
    
  ss << "Rank relation cache: " <<
    time2string(ranking_cache_time) << " s check time, " <<
    ranking_relations.hit << " hits, " <<
    ranking_relations.miss << " misses. ";  
  
  status(ss.str());
  ss.str("");
    
  ss << "Pointer analysis: " <<
    time2string(pointer_analysis_time) << " s total.";  
    
  status(ss.str());
  ss.str("");
  
  ss << "Loop reachability checks: " <<
    time2string(loop_reachability_time) << " s total.";  
      
  status(ss.str());
  ss.str("");
  
  ss << "Paths: " <<
    paths_analyzed << " seen, " <<
    paths_infeasible << " infeasible, " <<
    time2string(path_feasibility_time) << " s feasibility check time.";  
    
  status(ss.str());  
  ss.str("");
  
  ss << "Precondition checks: " <<
    time2string(wp_ce_extraction_time+wp_unreachability_time) << " s total, " <<
    time2string(wp_ce_extraction_time) << " s counterexample extraction, " <<
    time2string(wp_unreachability_time) << " s unreachability checks.";  
    
  status(ss.str());
  
  termination_baset::show_stats();
}

/********************************************************************\

 Function: termination_path_enumerationt::operator()

 Inputs:

 Outputs:

 Purpose: "Rank Function First" termination checks 

\********************************************************************/

termination_resultt termination_path_enumerationt::operator()()
{
  // Precondition: program must be termination-instrumented
  
  // free some memory - we won't need this data anymore.
  value_set_analysis.clear();
  invariant_propagation.clear();  
  
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
        termination_resultt res=T_NONTERMINATING;
        
        try 
        {
          res=terminates(main, goto_functions, assertion);
        }
        catch (const std::bad_alloc &e)
        {
          res=T_NONTERMINATING;
        }
        
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

