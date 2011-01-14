/*******************************************************************\

Module: Abstracting slicer for termination checks

Author: CM Wintersteiger

\*******************************************************************/

#include <fstream>
#include <map>
#include <stack>
#include <queue>

#include <find_symbols.h>
#include <prefix.h>
#include <i2string.h>

#include <goto-programs/cfg.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/remove_unreachable.h>
#include <goto-programs/remove_unused_functions.h>

#include "termination_slicer.h"
#include "find_symbols_rw.h"

#define forall_cfg_entries(it, cfg) \
   for(slicer_cfgt::entry_mapt::iterator it=(cfg).entry_map.begin(); \
       it!=(cfg).entry_map.end(); it++)

#define forall_cfg_predecessors(it, e) \
  for(slicer_cfgt::entryt::entriest::const_iterator it= \
        (e).predecessors.begin(); \
      it!=(e).predecessors.end(); it++)

#define forall_cfg_successors(it, e) \
  for(slicer_cfgt::entryt::entriest::const_iterator it= \
        (e).successors.begin(); \
      it!=(e).successors.end(); it++)


static std::string termination_prefix = "termination::pre::";

class termination_slicert : public messaget
{
public:
  termination_slicert(
    const contextt &_c,
    contextt &_sc,
    const goto_functionst &_srcf,
    const irep_idt &_entry,
    goto_programt::const_targett &_goal,
    goto_programt::targett &_dest_goal,
    goto_functionst &_dest,
    message_handlert &_mh) :
      messaget(_mh),
      abstract_loops(true),
      dependency_limit(5),
      replace_dynamic_allocation(false),
      ns(_c, _sc),
      shadow_context(_sc),
      src_functions(_srcf),
      entry(_entry),
      goal(_goal),
      dest_goal(_dest_goal),
      dest_functions(_dest) {}

    bool self_loops;
    bool abstract_loops;
    unsigned dependency_limit;
    bool replace_dynamic_allocation;

    void operator()();

protected:
    // convenience typedefs.
    typedef goto_functionst::goto_functiont goto_functiont;
    typedef goto_programt::const_targett const_targett;
    typedef goto_programt::targett targett;

    class dependency_sett : public find_symbols_sett
    {
    public:
      // we track everything that's in the path dependencies of the
      // assertion, up to a magic limit of X entries in the dependency set
      static unsigned magic_limit;

      dependency_sett() {}
      bool join(const dependency_sett &other);
      bool is_top() const { return (size()==1 && *begin()=="EVERYTHING"); }
      void make_top() { clear(); insert("EVERYTHING"); }
    };

    class dependenciest :
      public std::map<irep_idt, dependency_sett >
    {
    public:
      dependenciest() {};
      bool join(const dependenciest &other);
      bool depends(const irep_idt &id) const;
    };

    class slicer_cfg_entryt
    {
    public:
      slicer_cfg_entryt() : is_reachable(false) {}
      bool is_reachable;
      dependenciest dependencies;
      find_symbols_sett path_dependencies;
      bool depends(const irep_idt &id) const;
    };
    typedef cfg_baset<slicer_cfg_entryt> slicer_cfgt;
    
    typedef std::priority_queue<slicer_cfgt::iterator> queuet;

    const namespacet ns;
    contextt &shadow_context;
    const goto_functionst &src_functions;
    const irep_idt &entry;
    const_targett &goal;
    targett &dest_goal;

    goto_functionst &dest_functions;
    slicer_cfgt cfg;

    void copy_function(
      const goto_functionst::goto_functiont &src,
      goto_functionst::goto_functiont &dest) const;

    targett get_required_functions();

    bool slice();
    void fixedpoint_path_dependencies();
    void fixedpoint_data_dependencies();
    bool reduce();
    void kill_loops();
    void remove_unused_declarations();
    void remove_dynamic_allocation();

    void kill_loop(
      goto_programt &program,
      targett lstart,
      targett lend);

    void output(std::ostream &out) const;

    void show_dependencies(
      std::ostream &out,
      const dependenciest &dep) const;
};

unsigned termination_slicert::dependency_sett::magic_limit;

/********************************************************************\

 Function: termination_slicert::dependency_sett::join()

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool termination_slicert::dependency_sett::join(const dependency_sett &other)
{
  if(is_top()) return false;

  bool res=false;

  for(const_iterator it=other.begin(); it!=other.end(); it++)
  {
    if(insert(*it).second)
    {
      res=true;

      if(size()>magic_limit)
        make_top();
    }
  }

  return res;
}

/********************************************************************\

 Function: termination_slicert::dependenciest::join()

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool termination_slicert::dependenciest::join(const dependenciest &other)
{
  bool res=false;

  for(const_iterator it=other.begin(); it!=other.end(); it++)
  {
    const irep_idt &id=it->first;
    const dependency_sett &new_values=it->second;

    if(find(id)==end())
      continue; // not tracked!

    dependency_sett &old_values=operator[](id);
    if(old_values.join(new_values))
      res=true;
  }

  return res;
}

/********************************************************************\

 Function: termination_slicert::dependenciest::depends

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool termination_slicert::dependenciest::depends(const irep_idt &id) const
{
  for(const_iterator it=begin(); it!=end(); it++)
    if(it->second.find(id)!=it->second.end())
      return true;

  return false;
}

/********************************************************************\

 Function: termination_slicert::slicer_cfg_entryt::depends

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool termination_slicert::slicer_cfg_entryt::depends(const irep_idt &id) const
{
  if(path_dependencies.find(id)!=path_dependencies.end())
    return true; // path dependency

  if(dependencies.depends(id))
      return true; // data dependency

  return false;
}

/********************************************************************\

 Function: termination_slicert::slice()

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool termination_slicert::slice()
{
  dependency_sett::magic_limit = dependency_limit;
  cfg(dest_functions);

  status("Path Dependency Analysis...");
  fixedpoint_path_dependencies();

  status("Data Dependency Analysis...");
  fixedpoint_data_dependencies();

#if 0
  std::ofstream out("dependencies");
  output(out);
  out.close();
#endif

  status("Slicing...");
  return reduce();
}

/********************************************************************\

 Function: termination_slicert::fixedpoint()

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void termination_slicert::fixedpoint_data_dependencies()
{
//  const slicer_cfgt::entryt &goal_e=cfg.entries[dest_goal];
  queuet queue;

//  const find_symbols_sett &req_variables=goal_e.path_dependencies;
    
  queue.push(&cfg.entry_map[dest_goal]); // start from the assertion

  while(!queue.empty())
  {
    slicer_cfgt::iterator t=queue.top(); queue.pop();
    slicer_cfgt::entryt &e=*t;
    bool new_data=false;

    if(!e.is_reachable) new_data=true;
    e.is_reachable=true;

    // make sure we track all required variables
    if(e.dependencies.size()!=e.path_dependencies.size())
    {
      for(find_symbols_sett::const_iterator it=e.path_dependencies.begin();
          it!=e.path_dependencies.end();
          it++)
      {
        if(e.dependencies.find(*it)==e.dependencies.end())
        {
          e.dependencies[*it].clear();
          new_data=true;
        }
      }
    }

    // Propagate
    forall_cfg_successors(it, e)
    {
      const slicer_cfg_entryt &se=*(static_cast<slicer_cfg_entryt*>(*it));
      if(e.dependencies.join(se.dependencies))
        new_data=true;
    }

    // New values?
    switch(t->PC->type)
    {
      case ASSIGN:
      {
        const code_assignt &code=to_code_assign(t->PC->code);
        dependency_sett lhs_symbols, rhs_symbols;
        find_symbols_rw(code.lhs(), code.rhs(),
                        lhs_symbols, rhs_symbols);


        for(dependency_sett::const_iterator it=lhs_symbols.begin();
            it!=lhs_symbols.end();
            it++)
        {
          find_symbols_sett::iterator fit=e.path_dependencies.find(*it);
          if(fit==e.path_dependencies.end())
            continue; // not tracked

          dependency_sett &new_values=e.dependencies[*it];
          dependency_sett old_values;
          old_values.swap(new_values);

          for(dependency_sett::const_iterator rit=rhs_symbols.begin();
              rit!=rhs_symbols.end();
              rit++)
          {
            new_values.insert(*rit);
            if(old_values.find(*rit)==old_values.end())
              new_data=true;
          }
        }

        break;
      }

      case ASSUME:
      case ASSERT:
      case GOTO:
      case OTHER:
      case DECL:
      case SKIP:
      case LOCATION:
      case FUNCTION_CALL:
      case RETURN:
      case END_FUNCTION:
      case DEAD:
      case START_THREAD:
      case END_THREAD:
      case ATOMIC_BEGIN:
      case ATOMIC_END:
      {
        // all other instructions just propagate
        // i.e., nothing to do here.
        break;
      }

      case NO_INSTRUCTION_TYPE:
      default:
        throw "Unexpected instruction type";
    }

    if(new_data)
      forall_cfg_predecessors(it, e)
      {
        assert(*it==&cfg.entry_map[(*it)->PC]);
        queue.push(*it);
      }
  }
}

/********************************************************************\

 Function: termination_slicert::fixedpoint_path_dependencies()

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void termination_slicert::fixedpoint_path_dependencies()
{
  queuet queue;

  forall_goto_functions(fit, dest_functions)
    forall_goto_program_instructions(it, fit->second.body)
      if(it->type==ASSERT || it->type==ASSUME || it->type==GOTO)
        queue.push(&cfg.entry_map[it]);

  while(!queue.empty())
  {
    slicer_cfgt::iterator t=queue.top(); queue.pop();
    slicer_cfgt::entryt &e=*t;
    bool new_data=false;

    // inflow
    forall_cfg_successors(it, e)
    {
      slicer_cfg_entryt &se=cfg.entry_map[(*it)->PC];

      for(find_symbols_sett::const_iterator sit=se.path_dependencies.begin();
          sit!=se.path_dependencies.end();
          sit++)
      {
        if(e.path_dependencies.insert(*sit).second)
          new_data=true;
      }

      switch((*it)->PC->type)
      {
        case ASSIGN:
        {
          const code_assignt &code=to_code_assign((*it)->PC->code);
          find_symbols_sett lhss, rhss;
          find_symbols_rw(code.lhs(), code.rhs(), lhss, rhss);

          // If we depend on the LHS, we now depend on the RHS as well.

          bool depends=false;
          for(find_symbols_sett::const_iterator it=lhss.begin();
              it!=lhss.end();
              it++)
            if(e.path_dependencies.find(*it)!=e.path_dependencies.end())
              { depends=true; }

          if(depends)
          {
            for(find_symbols_sett::const_iterator it=rhss.begin();
                it!=rhss.end();
                it++)
              if(e.path_dependencies.insert(*it).second)
                new_data=true;
          }
          break;
        }
        case DECL:
        {
          // Coming from a decl of a variable that we depend on,
          // we can safely remove that variable.

          const codet &code=to_code((*it)->PC->code);

          assert(code.operands().size()==1 && code.op0().id()=="symbol");

          if(e.path_dependencies.erase(code.op0().get("identifier"))!=0)
            new_data=true;

          break;
        }
        default:
          /* Nothing */ ;
      }
    }

    switch(t->PC->type)
    {
      case ASSUME:
      {
        find_symbols_sett symbols;
        find_symbols(t->PC->guard, symbols);

        // If we depend on one of the symbols, we depend on all of them.

        bool depends=false;
        for(find_symbols_sett::const_iterator it=symbols.begin();
            it!=symbols.end();
            it++)
        {
          if(e.path_dependencies.find(*it)!=e.path_dependencies.end())
          {
            depends=true;
            break;
          }
        }

        if(depends)
          for(find_symbols_sett::const_iterator it=symbols.begin();
              it!=symbols.end();
              it++)
          {
            if(e.path_dependencies.insert(*it).second)
              new_data=true;
          }

        break;
      }
      case GOTO:
      case ASSERT: // we depend on everything, unconditionally
      {
        find_symbols_sett symbols;
        find_symbols(t->PC->guard, symbols);

        for(find_symbols_sett::const_iterator it=symbols.begin();
            it!=symbols.end();
            it++)
        {
          if(e.path_dependencies.insert(*it).second)
            new_data=true;
        }

        break;
      }

      case ASSIGN:
      {
        const code_assignt &code=to_code_assign(t->PC->code);

        if(code.lhs().id()=="symbol" &&
           code.rhs().id()=="symbol" &&
           has_prefix(code.lhs().get("identifier").as_string(),
                      termination_prefix))
        {
          // these instructions are very special: nothing depends
          // on them _yet_, but the termination analysis may find out
          // that it actually does. I.e., if we depend on the RHS,
          // we also need this instruction.

          if((e.path_dependencies.find(code.rhs().get("identifier"))!=
              e.path_dependencies.end()) &&
             e.path_dependencies.insert(code.lhs().get("identifier")).second)
              new_data=true;
        }

        break;
      }
      case DECL:
      case OTHER:
      case SKIP:
      case LOCATION:
        break;

      case FUNCTION_CALL:
      case RETURN:
      case END_FUNCTION:
        break;

      case DEAD:
      case START_THREAD:
      case END_THREAD:
      case ATOMIC_BEGIN:
      case ATOMIC_END:
        throw "NYI";

      case NO_INSTRUCTION_TYPE:
      default:
        throw "Unexpected instruction type";
    }

    if(new_data)
      forall_cfg_predecessors(it, e)
      {
        assert(*it==&cfg.entry_map[(*it)->PC]);
        queue.push(*it);
      }
  }
}

/*******************************************************************\

Function: termination_slicert::show_dependencies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void termination_slicert::show_dependencies(
  std::ostream &out,
  const dependenciest &dep) const
{
  if(dep.empty())
    out << "NO DEPENDENCIES" << std::endl;
  else
    for(dependenciest::const_iterator it=dep.begin();
        it!=dep.end();
        it++)
    {
      out << it->first << " |->";

      if(it->second.empty())
        out << " *** EMPTY *** " << std::endl;
      else
      {
        for(find_symbols_sett::const_iterator dit=it->second.begin();
            dit!=it->second.end();
            dit++)
        {
          if(dit!=it->second.begin()) out << ",";
          out << " " << *dit;
        }
        out << std::endl;
      }
    }
}

/*******************************************************************\

Function: termination_slicert::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void termination_slicert::output(std::ostream &out) const
{
  forall_goto_functions(f_it, dest_functions)
  {
    out << "Function: " << f_it->first << std::endl;
    out <<
      "==================================================" << std::endl;

    forall_goto_program_instructions(i_it, f_it->second.body)
    {
      slicer_cfgt::entry_mapt::const_iterator s=cfg.entry_map.find(i_it);
      if(s==cfg.entry_map.end()) continue;

      const slicer_cfgt::entryt &e=s->second;

      f_it->second.body.output_instruction(ns, "", out, i_it);

      out << "PATH: ";
      for(find_symbols_sett::const_iterator it=e.path_dependencies.begin();
          it!=e.path_dependencies.end();
          it++)
      {
        if(it!=e.path_dependencies.begin()) out << ",";
        out << " " << *it;
      }
      out << std::endl;

      show_dependencies(out, e.dependencies);
    }

    out << std::endl;
  }
}

/*******************************************************************\

Function: termination_slicert::reduce

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool termination_slicert::reduce()
{
  // now replace those instructions that do not reach any assertions
  // by self-loops

  Forall_goto_functions(f_it, dest_functions)
    if(f_it->second.body_available)
    {
      Forall_goto_program_instructions(i_it, f_it->second.body)
      {
        const slicer_cfg_entryt &e=cfg.entry_map[i_it];

        if(!e.is_reachable &&
           !i_it->is_end_function())
        {
          if(self_loops)
            i_it->make_goto(i_it);
          else
          {
            if (i_it->is_goto())
              i_it->make_goto(--f_it->second.body.instructions.end());
            else
              i_it->make_assumption(false_exprt());
          }
        }
        else
        {
          switch(i_it->type)
          {
            case ASSIGN:
            {
              code_assignt &code=to_code_assign(i_it->code);
              find_symbols_sett lhs_symbols;
              find_symbols_w(code.lhs(), lhs_symbols);

              bool is_alive=false;
              bool too_complex=false;

              for(find_symbols_sett::const_iterator sit=lhs_symbols.begin();
                  sit!=lhs_symbols.end() && !is_alive;
                  sit++)
              {
                // does anybody in the future depend on me?
                if(!is_alive && e.depends(*sit))
                  is_alive=true;

                // am I too complex?
                dependenciest::const_iterator fit=e.dependencies.find(*sit);
                if(fit!=e.dependencies.end() && fit->second.is_top())
                  too_complex=true;
              }

              if(is_alive && too_complex)
              {
                exprt ne("sideeffect", code.lhs().type());
                ne.set("statement", "nondet");
                code.rhs() = ne;
              }

              if(!is_alive)
                i_it->make_skip();

              break;
            }
            case ASSUME:
            {
              find_symbols_sett symbols;
              find_symbols_w(i_it->guard, symbols);

              bool required=false;
              for(find_symbols_sett::const_iterator it=symbols.begin();
                  it!=symbols.end();
                  it++)
              {
                if(e.path_dependencies.find(*it)!=e.path_dependencies.end())
                {
                  required=true;
                  break;
                }
              }

              if(!required)
                i_it->make_skip();
            }
            default:
              /* ignore */ ;
          }
        }
      }

      // replace unreachable code by skip
      remove_unreachable(f_it->second.body);
    }

  if(dest_goal->is_skip()) // this means it was found to be unreachable
    return false;

  remove_unused_declarations();

  // remove the skips
  remove_skip(dest_functions);
  dest_functions.update();

  // be nice...
  Forall_goto_functions(it, dest_functions)
    Forall_goto_program_instructions(i_it, it->second.body)
      i_it->function=it->first;

  return true;
}

/********************************************************************\

 Function: termination_slicert::remove_unused_declarations

 Inputs:

 Outputs:

 Purpose: removes unused decl-statements

\********************************************************************/

void termination_slicert::remove_unused_declarations()
{
  queuet queue;
  find_symbols_sett used_variables; // flow-insensitive
  std::set<slicer_cfgt::iterator> seen;

  queue.push(&cfg.entry_map[dest_goal]);

  while(!queue.empty())
  {
    slicer_cfgt::iterator t=queue.top(); queue.pop();
    slicer_cfgt::entryt &e=*t;

    if(seen.find(t)!=seen.end())
      continue;

    seen.insert(t);

    switch(t->PC->type)
    {
      case ASSUME:
      case ASSERT:
      case GOTO:
        find_symbols(t->PC->guard, used_variables);
        break;
      case DECL: /* ignore */ break;
      default:
        find_symbols(t->PC->code, used_variables);
    }

    forall_cfg_predecessors(it, e)
    {
      assert(*it==&cfg.entry_map[(*it)->PC]);
      queue.push(*it);
    }
  }

  // now kill all useless decls.

  Forall_goto_functions(it, dest_functions)
    Forall_goto_program_instructions(i_it, it->second.body)
    {
      if(i_it->type==DECL)
      {
        const codet &code=to_code(i_it->code);

        const irep_idt &ident=code.op0().get("identifier");

        if(used_variables.find(ident)==used_variables.end())
          i_it->make_skip();
      }
    }
}


/********************************************************************\

 Function: termination_slicert::copy_function

 Inputs:

 Outputs:

 Purpose: copies a goto function

\********************************************************************/

void termination_slicert::copy_function(
  const goto_functionst::goto_functiont &src,
  goto_functionst::goto_functiont &dest) const
{
  dest.body.copy_from(src.body);
  dest.body_available=src.body_available;
  dest.type=src.type;
}

/********************************************************************\

 Function: termination_slicert::get_required_functions

 Inputs:

 Outputs:

 Purpose:  returns a pointer to the destination assertion

\********************************************************************/

goto_programt::targett termination_slicert::get_required_functions()
{
  // first, copy the entry-point
  goto_functionst::function_mapt::const_iterator mit=
      src_functions.function_map.find(entry);

  assert(mit!=src_functions.function_map.end());
  const goto_functiont &src=mit->second;

  goto_functiont &dest=dest_functions.function_map[entry];
  copy_function(src, dest);

  // iterate through both programs at the same time
  const_targett it=src.body.instructions.begin();
  const_targett end=src.body.instructions.end();
  targett dit=dest.body.instructions.begin();
  targett dend=dest.body.instructions.end();
  targett res=dend;
  bool found=false;

  std::stack<std::pair<const_targett, targett> > recstack;
  recstack.push(std::make_pair(end, dend));

  while(!recstack.empty() && it!=end)
  {
    assert(it->type==dit->type);

    if(it==goal)
    {
      res=dit; // found it!
      found=true;
    }

    switch(it->type)
    {
      case ASSERT:
        if(it!=goal) dit->make_skip();
        it++;
        dit++;
        break;

      case FUNCTION_CALL:
      {
        const code_function_callt &code=to_code_function_call(it->code);
        const irep_idt &fid=code.function().get("identifier");

        goto_functionst::function_mapt::const_iterator fit=
            src_functions.function_map.find(fid);

        if(fit==src_functions.function_map.end())
        {
          it++; // ignore the call
          dit++;
        }
        else
        {
          // copy the function to dest, if not there.
          goto_functionst::function_mapt::const_iterator dfit=
            dest_functions.function_map.find(fid);

          if(dfit==dest_functions.function_map.end()) // not there yet
          {
            goto_functiont &nfunc=dest_functions.function_map[fid];
            copy_function(fit->second, nfunc);

            recstack.push(std::make_pair(it, dit));
            it=fit->second.body.instructions.begin();
            dit=nfunc.body.instructions.begin();
          }
          else
          {
            it++; // don't do it again.
            dit++;
          }
        }
        break;
      }
      case END_FUNCTION:
        if(!recstack.empty())
        {
          it=recstack.top().first;
          dit=recstack.top().second;
          recstack.pop();
        }
        it++;
        dit++;
        break;
      default:
        it++;
        dit++;
    }
  }

  return res;
}

/********************************************************************\

 Function: termination_slicert::kill_loop

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void termination_slicert::kill_loop(
  goto_programt &program,
  targett lstart,
  targett lend)
{
  assert(lend->is_backwards_goto());
  exprt guard=lend->guard;

  std::set<exprt> written_symbols;

  // required in case the target is a sub-loop
  targett dest_bj=program.instructions.end();

  bool in_sub=false;
  for(targett lit=lstart; lit!=lend; lit++)
  {
    if(lit->type==ASSIGN)
    {
      const code_assignt &code=to_code_assign(lit->code);
      find_symbols_w(code.lhs(), written_symbols);
    }

    if(in_sub)
    {
      if(lit==dest_bj)
        in_sub=false;
    }
    else // !in_sub
    {
      if(lit==dest_goal)
      {
        in_sub=true;
        dest_bj=dest_goal;
        while(dest_bj->type!=GOTO ||
              dest_bj->targets.front()!=dest_goal)
          dest_bj++;
        assert(dest_bj->is_backwards_goto());
      }
      else
        // We need to kill everything, except function calls!
        if(lit->type!=FUNCTION_CALL)
          lit->make_skip();
    }
  }

  lend->make_skip();
  
  // assert(!in_sub); // We did exit the sub-loop!
  // Not necessarily the case for weird 8-type loops.

  #if 0
  for(std::set<exprt>::const_iterator it=written_symbols.begin();
      it!=written_symbols.end();
      it++)
    std::cout << "WRITTEN: " << *it << std::endl;
  #endif

  // make some room for those nondet-assignments
  for(unsigned i=0; i < written_symbols.size(); i++)
    program.insert_before(lstart)->make_skip();

  for(std::set<exprt>::const_iterator sit=written_symbols.begin();
      sit!=written_symbols.end();
      sit++)
  {
    assert(dest_goal->guard.operands().size()==2 &&
           dest_goal->guard.id()=="=>" &&
           dest_goal->guard.op0().id()=="symbol"); // this must be the copied-flag

    goto_programt::targett new_assign=program.insert_before(lstart);

    if(*sit==dest_goal->guard.op0())
    {
      // We see the current copied-flag - this is always set to false,
      // not to a non-deterministic value.

      assert(sit->type().id()=="bool");
      new_assign->make_assignment();
      new_assign->code=code_assignt(*sit, false_exprt());
    }
    else
    {
      exprt ne("sideeffect", sit->type());
      ne.set("statement", "nondet");

      new_assign->make_assignment();
      new_assign->code=code_assignt(*sit, ne);
    }
  }

  if(!guard.is_true())
    program.insert_after(lend)->make_assumption(not_exprt(guard));
}

/********************************************************************\

 Function: termination_slicert::kill_loops()

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void termination_slicert::kill_loops()
{
  status("Abstracting loops...");

  goto_functionst::function_mapt::iterator eit=
      dest_functions.function_map.find(entry);

  assert(eit!=dest_functions.function_map.end());
  goto_functiont &func=eit->second;

  // find the corresponding backjump (to kill loops in loops)
  targett last=dest_goal;
  while((!last->is_goto() ||
         last->targets.front()!=dest_goal) &&
        last!=func.body.instructions.end())
    last++;
  assert(last->is_backwards_goto());

  Forall_goto_functions(fit, dest_functions)
    Forall_goto_program_instructions(it, fit->second.body)
    {
      if(it!=last && it->is_backwards_goto())
      {
        assert(it->targets.size()==1);
        kill_loop(fit->second.body, it->targets.front(), it);
      }
    }
}

/********************************************************************\

 Function: termination_slicert::remove_dynamic_allocation

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void termination_slicert::remove_dynamic_allocation()
{
  unsigned object_count=0;

  Forall_goto_functions(fit, dest_functions)
    Forall_goto_program_instructions(it, fit->second.body)
      if(it->type==ASSIGN &&
         it->code.op1().id()=="sideeffect" &&
         it->code.op1().get("statement")=="malloc")
      {
//        std::cout << "CODE: " << it->code << std::endl;
        code_assignt &code=to_code_assign(it->code);

        const exprt &size=code.rhs().find_expr("#size");
        const typet &type=(typet&) code.rhs().find("#type");

        irep_idt new_id;
        symbolt* new_symbolp;
        symbolt new_symbol;

        do
        {
          new_id = "dynamic_object"+i2string(++object_count);

          new_symbol.name="termination::"+new_id.as_string();
          new_symbol.base_name=new_id;
          new_symbol.type=array_typet();
          new_symbol.type.subtype()=type;

          if(size.is_constant())
            new_symbol.type.set("size", size);
          else
            new_symbol.type.set("size", "infinity");
        }
        while (shadow_context.move(new_symbol, new_symbolp));

        code.rhs()=typecast_exprt(code.lhs().type());
        code.rhs().op0()=symbol_exprt(new_symbolp->name, new_symbolp->type);

        it++; it->make_skip(); // Assumption;
        it++; it->make_skip(); // alloc_size = ...
        it++; it->make_skip(); // alloc = ...
      }
}

/********************************************************************\

 Function: termination_slicert::operator()

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void termination_slicert::operator()()
{
  goto_functionst::function_mapt::const_iterator mit=
      src_functions.function_map.find(entry);

  if(mit!=src_functions.function_map.end())
  {
    dest_goal=get_required_functions();
    assert(dest_goal->type==ASSERT);

    if(abstract_loops)
    {
      kill_loops();

      #if 0
      std::ofstream f("abstracted_model");
      dest_functions.output(ns, f);
      f.close();
      #endif
    }

    if(replace_dynamic_allocation)
      remove_dynamic_allocation();

    if(!slice())
    {
      // Assertion unreachable!
      dest_goal=goto_programt::targett(0);
    }

    remove_unused_functions(dest_functions, get_message_handler());
  }
  else
    warning("Entry point not found");
}

/********************************************************************\

 Function: sliced_abstraction

 Inputs:

 Outputs:

 Purpose: Puts a slice into dest

\********************************************************************/

bool sliced_abstraction(
  const contextt &context,
  contextt &shadow_context,
  const goto_functionst &src_functions,
  const irep_idt &entry,
  goto_programt::const_targett &to,
  goto_programt::targett &sliced_assertion,
  goto_functionst &dest_functions,
  message_handlert &message_handler,
  bool self_loops,
  bool abstract_loops,
  unsigned dependency_limit,
  bool replace_dynamic_allocation)
{
  assert(to->type==ASSERT);
  dest_functions.clear();

  termination_slicert termination_slicer(context,
                                         shadow_context,
                                         src_functions,
                                         entry,
                                         to,
                                         sliced_assertion,
                                         dest_functions,
                                         message_handler);

  termination_slicer.self_loops=self_loops;
  termination_slicer.abstract_loops=abstract_loops;
  termination_slicer.dependency_limit=dependency_limit;
  termination_slicer.replace_dynamic_allocation=replace_dynamic_allocation;

  termination_slicer();

  return sliced_assertion!=goto_programt::targett(0);
}
