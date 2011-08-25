/*******************************************************************

 Module: Loop Transformations

 Author: CM Wintersteiger

\*******************************************************************/

#include <fstream>
#include <message_stream.h>
#include <i2string.h>
#include <ansi-c/c_types.h>
#include <expr_util.h>
#include <std_expr.h>
#include <arith_tools.h>

#include "transform_loops.h"

#define forall_goto_targets(it, goto_ins) \
    for(goto_programt::targetst::const_iterator it= \
          (goto_ins)->targets.begin(); \
        it!=(goto_ins)->targets.end(); \
        it++)

#define Forall_goto_targets(it, goto_ins) \
    for(goto_programt::targetst::iterator it= \
          (goto_ins)->targets.begin(); \
        it!=(goto_ins)->targets.end(); \
        it++)

#define forall_incoming_edges(it, goto_ins) \
  for(std::set<goto_programt::targett>::const_iterator it = \
        (goto_ins)->incoming_edges.begin(); \
      it!=(goto_ins)->incoming_edges.end(); \
      it++)

#define Forall_incoming_edges(it, goto_ins) \
  for(std::set<goto_programt::targett>::iterator it = \
        (goto_ins)->incoming_edges.begin(); \
      it!=(goto_ins)->incoming_edges.end(); \
      it++)

// a helper class to make the code look nicer
class block_numberst :
  public std::map<goto_programt::targett, unsigned>
{
public:
  unsigned get(goto_programt::targett &target)
  {
    std::map<goto_programt::targett, unsigned>::const_iterator t =
      find(target);

    if(t!=end())
      return t->second;
    else
    {
      unsigned newindex = size();
      operator[](target)=newindex;
      return newindex;
    }
  }
};

/*******************************************************************\

Function: loop_transformt::transform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void loop_transformt::transform(goto_functionst &goto_functions)
{
  for(goto_functionst::function_mapt::iterator it=
        goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
  {
    if(it->second.body_available)
    {
      #if 0
      static fcount = 0;
      std::stringstream fn, of;
      fn << "dot/function_" << ++fcount << ".dot";
      write_dot_graph(it->second.body, it->first.as_string(), fn.str());
      #endif

      transform(it->second.body);
    }
  }
}

/*******************************************************************\

Function: loop_transformt::transform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void loop_transformt::transform(goto_programt &goto_program)
{
  goto_program.compute_incoming_edges();

  // pass 1: simple stuff
  Forall_goto_program_instructions(it, goto_program)
    if(it->is_backwards_goto())
    {
      assert(it->targets.size()==1);

      goto_programt::targett begin = it->targets.front();
      goto_programt::targett end = it;

      split_multi_head(goto_program, begin, end);
      transform_do_while(goto_program, begin, end);
      move_returns(goto_program, begin, end);
    }

  // pass 2: loop simulation
  Forall_goto_program_instructions(it, goto_program)
    if(it->is_backwards_goto())
    {
      goto_programt::targett begin = it->targets.front();
      goto_programt::targett end = it;

      std::set<goto_programt::targett> entries;
      std::set<goto_programt::targett> exits;

      analyze(goto_program, begin, end, entries, exits);
      transform(goto_program, begin, end, entries, exits);

      it=end;
    }

  goto_program.update();

  #if 1
  // Another run for debugging
  forall_goto_program_instructions(it, goto_program)
    if(it->is_backwards_goto())
    {
      goto_programt::const_targett begin = it->targets.front();
      goto_programt::const_targett end = it;

      run_checks(goto_program, begin, end);
    }
  #endif
}

/*******************************************************************\

Function: loop_transformert::transform_do_while

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void loop_transformt::transform_do_while(
  goto_programt &program,
  goto_programt::targett &begin,
  goto_programt::targett &end) const
{
  if(!end->guard.is_true())
  {
    #if 0
    std::cout << "TRANSFORM DO-WHILE" << std::endl;
    #endif

    goto_programt::targett next = end; next++;
    assert(next!=program.instructions.end());

    goto_programt::instructiont newguard;
    newguard.make_goto(next);
    newguard.guard = end->guard;
    newguard.guard.make_not();
    newguard.location = end->location;
    end->guard.make_true();

    unsigned ln = end->location_number; // doesn't get swapped
    program.insert_before_swap(end, newguard); // end now points to the new guard

    goto_programt::targett old_guard = end; old_guard++;
    end->location_number=ln;
    old_guard->location_number=ln;

    program.update();

    #if 0
    std::cout << "Transformed: " << std::endl;
    goto_programt::const_targett it = begin;
    for (;
         it!=end;
         it++)
      program.output_instruction(ns, "", std::cout, it);
    program.output_instruction(ns, "", std::cout, it);
    #endif
  }
}

/*******************************************************************\

Function: loop_transformt::split_multi_head

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void loop_transformt::move_returns(
  goto_programt &program,
  goto_programt::targett begin,
  goto_programt::targett end)
{
  goto_programt::targett postend = end; postend++;

  std::list<goto_programt::targett> returns;

  for(goto_programt::targett it = begin;
      it!=end;
      it++)
  {
    if(it->is_return())
      returns.push_back(it);
  }

  if(returns.size()>0)
  {
    for(std::list<goto_programt::targett>::const_iterator it = returns.begin();
        it!=returns.end();
        it++)
    {

      goto_programt::targett newret = program.insert_before(postend);
      newret->swap(**it);
      newret->location_number = postend->location_number;      

      (*it)->make_goto(newret);
      // this creates far exits,
      // which will be fixed lateron
    }

    // fix the loop exit
    goto_programt::targett firstafter = end; firstafter++;
    goto_programt::targett loopexit = program.insert_before(firstafter);
    loopexit->make_goto(postend);
    
    program.update();
  }
}

/*******************************************************************\

Function: loop_transformt::split_multi_head

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void loop_transformt::split_multi_head(
  goto_programt &program,
  goto_programt::targett begin,
  goto_programt::targett end)
{
  #if 0
  std::cout << "SPLIT MULTI-HEAD (" << begin->incoming_edges.size() <<
    ")" << std::endl;
  #endif

  unsigned dontmatter = 0;
  goto_programt::targett prev = begin; prev--;
  
  forall_incoming_edges(it, begin)  
  {
    if((*it)==prev) dontmatter++;
    else if((*it)==end) dontmatter++;
  }
  
  if(begin->incoming_edges.size() > dontmatter)
  {
    #if 0
    std::cout << "Splitting " << begin->incoming_edges.size() <<
      "-head" << std::endl;
    #endif

    goto_programt::targett newskip = program.insert_before(begin);

    newskip->make_skip();
    newskip->location_number = begin->location_number;
    newskip->function = begin->function;
    newskip->location = begin->location;

    // redirect gotos
    forall_incoming_edges(it, begin)    
    {
      const goto_programt::targett &from = *it;
      
      if(from!=prev && from!=end &&
         from->is_goto() &&
         from->targets.front()==begin) // gotos right before the loop
                                       // aren't necessarily jumping to begin
      {
        assert(from->targets.size()==1);
        
        from->targets.clear();
        from->targets.push_back(newskip);
      }
    }

    program.update();

    #if 0
    namespacet ns(context);
    std::cout << "Split loop: " << std::endl;
    goto_programt::const_targett it = newskip;
    for (;
         it!=end;
         it++)
      program.output_instruction(ns, "", std::cout, it);
    program.output_instruction(ns, "", std::cout, it);
    #endif

    assert(begin->incoming_edges.size()<=2);
  }

}

/*******************************************************************\

Function: loop_transformt::check_loop_interleaved

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool loop_transformt::check_loop_interleaved(
  const goto_programt &program,
  goto_programt::const_targett begin,
  goto_programt::const_targett end)
{
  // assumes incoming edges are calculated

  goto_programt::const_targett next = begin; next++;

  // we start from next, since a backjump to the first
  // instruction is just a nested loop, as long as it's
  // not a backjump itself.
  assert(!begin->is_backwards_goto());

  for(goto_programt::const_targett it = next;
      it!=end;
      it++)
  {
    forall_incoming_edges(t_it, it)    
    {
      const goto_programt::targett &edge = *t_it;

      if(edge->location_number>end->location_number)
      {
        std::stringstream str;
        str << "Error: Interleaved loop: " <<
          it->location.get_file() << " " <<
          it->location.get_line();

        output_loop(std::cout, program, begin, end);
        throw str.str();
      }
    }
  }

  return false;
}

/*******************************************************************\

Function: loop_transformt::check_loop_exits

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool loop_transformt::check_loop_exits(
  const goto_programt &program,
  goto_programt::const_targett begin,
  goto_programt::const_targett end)
{
  goto_programt::const_targett exit = end; exit++;

  bool check = false;

  for(goto_programt::const_targett it = begin;
      it!=end;
      it++)
  {
    if(it->is_goto())
    {
      assert(it->targets.size()==1);
      goto_programt::const_targett target = it->targets.front();

      if(target->location_number > end->location_number &&
         target!=exit)
      {
        str << "Warning: Far loop exit: " <<
          it->location.get_file() << " " <<
          it->location.get_line();

//        std::cout << begin->function << " " << begin->location_number << " to " <<
//          end->location_number << std::endl;
//        std::cout << "LN: " << begin->function << " " << it->location_number << std::endl;
        warning();
        check = true;
      }
      else if(target->location_number < begin->location_number)
      {
        std::stringstream str;
        str << "Error: Backwards loop exit: " <<
          it->location.get_file() << " " <<
          it->location.get_line();
        throw str.str();
      }
    }
  }

  return check;
}

/*******************************************************************

 Function: transform_loopst::is_forward_entry

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool loop_transformt::is_forward_entry(
  const goto_programt::targett &loc,
  const goto_programt::targett &begin,
  const goto_programt::targett &end) const
{
  return loc->location_number < begin->location_number;
}

/*******************************************************************

 Function: transform_loopst::is_early_entry

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool loop_transformt::is_early_entry(
  const goto_programt::targett &loc,
  const goto_programt::targett &begin,
  const goto_programt::targett &end) const
{
  goto_programt::targett exit=end; exit++;
  goto_programt::targett prev=begin; prev--;

  return loc->location_number > exit->location_number ||
         loc->location_number < prev->location_number;
}

/*******************************************************************

 Function: transform_loopst::is_backward_entry

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool loop_transformt::is_backward_entry(
  const goto_programt::targett &loc,
  const goto_programt::targett &begin,
  const goto_programt::targett &end) const
{
  return loc->location_number > end->location_number;
}

/*******************************************************************

 Function: transform_loopst::is_exit

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool loop_transformt::is_exit(
  const goto_programt::targett &loc,
  const goto_programt::targett &begin,
  const goto_programt::targett &end) const
{
  return is_forward_exit(loc,begin,end) || is_backward_exit(loc,begin,end);
}

/*******************************************************************

 Function: transform_loopst::is_forward_exit

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool loop_transformt::is_forward_exit(
  const goto_programt::targett &loc,
  const goto_programt::targett &begin,
  const goto_programt::targett &end) const
{
  return loc->location_number > end->location_number;
}

/*******************************************************************

 Function: transform_loopst::is_in_loop

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool loop_transformt::is_in_loop(
  const goto_programt::targett &loc,
  const goto_programt::targett &begin,
  const goto_programt::targett &end) const
{
  return loc->location_number >= begin->location_number &&
         loc->location_number <= end->location_number;
}

/*******************************************************************

 Function: transform_loopst::is_backward_exit

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool loop_transformt::is_backward_exit(
  const goto_programt::targett &loc,
  const goto_programt::targett &begin,
  const goto_programt::targett &end) const
{
  return loc->location_number < begin->location_number;
}

/*******************************************************************

 Function: transform_loopst::is_far_exit

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool loop_transformt::is_far_exit(
  const goto_programt::targett &loc,
  const goto_programt::targett &begin,
  const goto_programt::targett &end) const
{
  goto_programt::targett exit=end; exit++;
  return loc->location_number > exit->location_number ||
         loc->location_number < begin->location_number;
}

/*******************************************************************

 Function: transform_loopst::recheck_exits

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void loop_transformt::recheck_exits(
  const goto_programt::targett &begin,
  const goto_programt::targett &end,
  std::set<goto_programt::targett> &exits) const
{
  std::set<goto_programt::targett> real_exits;

  for(std::set<goto_programt::targett>::iterator l_it=exits.begin();
      l_it!=exits.end();
      l_it++)
  {
    goto_programt::targett exit_target = (*l_it)->targets.front();

    if(is_exit(exit_target, begin, end))
      real_exits.insert(*l_it);
  }

  exits = real_exits;
}

/*******************************************************************\

Function: loop_transformt::analyze

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void loop_transformt::analyze(
  goto_programt &program,
  goto_programt::targett &begin,
  goto_programt::targett &end,
  std::set<goto_programt::targett> &entries,
  std::set<goto_programt::targett> &exits)
{
  #if 0
  std::cout << "ANALYZE: " << begin->function << " " << begin->location_number
    << " to " << end->location_number << std::endl;
  #endif

  goto_programt::targett prev = begin; prev--;
  goto_programt::targett exit = end; exit++;

  for(goto_programt::targett it = begin;
      it!=exit;
      it++)
  {
    // is this an entry point?
    forall_incoming_edges(i_it, it)
    {
      if(is_forward_entry(*i_it, begin, end))
        entries.insert(*i_it);

      if(is_backward_entry(*i_it, begin, end))
      {
        // this is a backjump from some location further down -
        // this means, we have an interleaved loop.
        // the analysis is thus extended to the end of that loop
        #if 0
        std::cout << "EXTENDING ANALYSIS on " <<
          it->location_number << std::endl;
        #endif

        entries.insert(end);
        end = *i_it; exit = end; exit++;

        // former exits may not be exits anymore, recheck
        recheck_exits(begin, end, exits);
      }
    }

    if(it->is_goto() && it!=end)
    {
      Forall_goto_targets(t_it, it)
      {
        if(is_forward_exit(*t_it, begin, end))
        {
          exits.insert(it);
        }
        else if(is_backward_exit(*t_it,begin,end))
        {
          #if 0
          std::cout << "BACKWARDS EXTENDING ANALYSIS on " <<
            it->location_number << std::endl;
          #endif
          entries.erase(prev);
          begin = *t_it; prev = begin; prev--;

          if(!(prev->is_return() ||
               (prev->is_goto() &&
                prev->guard.is_true() &&
                prev->targets.front()!=begin)))
             entries.insert(prev);

          // reset analysis
          it = prev;
          break;
        }
      }
    }
  }

  #if 0
  if(!(entries.size()<=1 && exits.size()<=1))
  {
    std::cout << begin->function << " " << begin->location_number << " to " <<
      end->location_number << std::endl;
    std::cout << "LOOP STATS: " << entries.size() << " entries, " <<
      exits.size() << " exits." << std::endl;
  }
  #endif
}

/*******************************************************************

 Function: transform_loopst::get_new_variable

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

exprt loop_transformt::get_new_variable(void)
{
  irep_idt ident;

  do
  {
    ident = "looptrans::loopvar$" + i2string(++trans_counter);
  }
  while(context.symbols.find(ident)!=context.symbols.end());

  symbolt newsym;
  newsym.name = ident;
  newsym.base_name = "loopvar$" + i2string(trans_counter);
  newsym.type = uint_type();

  exprt res("symbol", newsym.type);
  res.set("identifier", ident);

  context.move(newsym);

  return res;
}

/*******************************************************************\

Function: loop_transformt::transform_entries

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void loop_transformt::transform_entries(
  goto_programt &program,
  goto_programt::targett &begin,
  goto_programt::targett &end,
  const exprt &loop_symbol,
  std::set<goto_programt::targett> &entries)
{
  // end is not an entry
  assert(entries.find(end)==entries.end());

  #if 0
  std::cout << "ENTRIES: ";
  for(std::set<goto_programt::targett>::const_iterator it = entries.begin();
      it!=entries.end();
      it++)
    std::cout << (*it)->location_number << ", ";
  std::cout << std::endl;
  #endif

  goto_programt::targett prev = begin; prev--;
  goto_programt::targett postend = end; postend++;

  // a new backjump target.
  goto_programt::targett loop_start = program.insert_before(begin);
  loop_start->type = SKIP;
  loop_start->location_number = begin->location_number;
  //loop_start->labels.push_back("LOOP_HEAD");

  //program.target_numbers.insert(
  //          std::pair<goto_programt::targett, unsigned>(loop_start, 0));

  // a new backjump
  goto_programt::targett backjump = program.insert_before(postend);
  backjump->type = GOTO;
  backjump->guard.make_true();
  backjump->location_number = end->location_number;
  backjump->targets.push_back(loop_start);
  //backjump->labels.push_back("BACKJUMP");
  
  //program.target_numbers.insert(
  //            std::pair<goto_programt::targett, unsigned>(backjump, 0));

  // we assign numbers to blocks
  block_numberst block_numbers;
  block_numbers[begin]=0;

  // in addition to all entries,
  // we want to simulate all backjumps
  for(goto_programt::targett it=begin;
      it!=backjump;
      it++)
  {
    if(it->is_goto())
    {
      assert(!is_backward_exit(it->targets.front(), begin, end));

      if(it->is_backwards_goto())
      {
        entries.insert(it);

        #if 0
        std::cout << "Additional Entry: " << it->location_number << std::endl;
        #endif
      }
    }
  }

  for(std::set<goto_programt::targett>::const_iterator it=
        entries.begin();
      it!=entries.end();
      it++)
  {
    goto_programt::targett entry = *it;

    if(entry->is_goto() &&
       is_in_loop(entry->targets.front(), begin, end))
    {

      goto_programt::instructiont pre_entry;
      pre_entry.type=ASSIGN;
      pre_entry.function=entry->function;
      pre_entry.code=code_assignt(loop_symbol,
                         from_integer(block_numbers.get(entry->targets.front()),
                                    uint_type()));

      unsigned ln = entry->location_number; // gets swapped away
      program.insert_before_swap(entry, pre_entry);
      // entry now points to pre_entry, fix it:
      goto_programt::targett real_entry=entry; real_entry++;
      entry->location_number=ln;
      real_entry->location_number=ln;

      // set up the jump
      real_entry->targets.clear();

      if(is_early_entry(real_entry, begin, end))
      {
        #if 0
        std::cout << "EARLY ENTRY: " << entry->location_number << std::endl;
        #endif

        if(real_entry==prev)
          real_entry->make_skip();
        else
          real_entry->targets.push_back(loop_start);
      }
      else
      {
        #if 0
        std::cout << "BJ ENTRY: " << entry->location_number << std::endl;
        #endif

        real_entry->targets.push_back(backjump);
      }
    }
    else
    {
      #if 0
      std::cout << " NOT IN LOOP: " << entry->location_number << std::endl;
      #endif

      // this "flows" into begin anyways
      goto_programt::targett post_entry = entry; post_entry++;
      post_entry = program.insert_before(post_entry);
      post_entry->type=ASSIGN;
      post_entry->function=entry->function;
      post_entry->location_number=entry->location_number;
      post_entry->code=code_assignt(loop_symbol,
                                    from_integer(block_numbers.get(begin),
                                                 uint_type()));
    }
  }

  // create jumps to the blocks
  for(block_numberst::iterator it = block_numbers.begin();
      it!=block_numbers.end();
      it++)
  {
    if(it->second!=0) // the "flowing entry doesn't need it
    {
      goto_programt::targett newt = program.insert_before(begin);
      newt->type=GOTO;
      equality_exprt guard(loop_symbol, from_integer(it->second, uint_type()));
      newt->guard=guard;
      newt->targets.push_back(it->first);
      newt->location_number = begin->location_number;      
    }
  }

  begin = loop_start;
  end = backjump;  

  // incoming_edges are messed up now!  
  program.update();
}

/*******************************************************************\

Function: loop_transformt::transform_exits

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void loop_transformt::transform_exits(
  goto_programt &program,
  goto_programt::targett &begin,
  goto_programt::targett &end,
  const exprt &loop_symbol,
  std::set<goto_programt::targett> &exits)
{
  goto_programt::targett next=end; next++;

  #if 0
  std::cout << "EXITS: ";
  for(std::set<goto_programt::targett>::const_iterator it = exits.begin();
      it!=exits.end();
      it++)
    std::cout << (*it)->location_number << ", ";
  std::cout << std::endl;
  #endif

  goto_programt::targett exit_skip = program.insert_before(next);
  exit_skip->type = SKIP;
  //exit_skip->labels.push_back("EXIT_POINT");
  
  //program.target_numbers.insert(
  //              std::pair<goto_programt::targett, unsigned>(exit_skip, 0));

  // assign numbers to exits
  block_numberst exit_numbers;
  exit_numbers[next]=0;

  for(std::set<goto_programt::targett>::const_iterator it=
        exits.begin();
      it!=exits.end();
      it++)
  {
    goto_programt::targett exit = *it;

    assert(is_forward_exit(exit->targets.front(), begin, end));

    goto_programt::instructiont ass;
    ass.type=ASSIGN;
    ass.function=exit->function;
    ass.location_number=exit->location_number;
    ass.code=code_assignt(loop_symbol,
                           from_integer(exit_numbers.get(exit->targets.front()),
                                        uint_type()));

    unsigned ln = exit->location_number; // doesn't get swapped
    program.insert_before_swap(exit, ass);
    // exit now points to ass, fix it:
    goto_programt::targett real_exit=exit; real_exit++;
    exit->location_number=ln;
    real_exit->location_number=ln;

    // every exit points to next!
    real_exit->targets.clear();
    real_exit->targets.push_back(exit_skip);
  }

  // add exit goto for each of them
  for(block_numberst::const_iterator it=
        exit_numbers.begin();
      it!=exit_numbers.end();
      it++)
  {
    if(it->second!=0)
    {
      goto_programt::targett newt=program.insert_before(next);
      newt->type=GOTO;
      equality_exprt guard(loop_symbol, from_integer(it->second, uint_type()));
      newt->guard=guard;
      newt->location_number=next->location_number;
      newt->location=end->location;
      newt->targets.push_back(it->first);
    }
  }
  
  // incoming_edges are messed up now!
  program.update();
}

/*******************************************************************\

Function: loop_transformt::transform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void loop_transformt::transform(
  goto_programt &program,
  goto_programt::targett &begin,
  goto_programt::targett &end,
  std::set<goto_programt::targett> &entries,
  std::set<goto_programt::targett> &exits)
{
  goto_programt::targett next = end; next++;

  // check if we need to transform this loop
  bool all_exits_near=true;

  for(std::set<goto_programt::targett>::const_iterator it = exits.begin();
      it!=exits.end();
      it++)
  {
    if((*it)->targets.front()!=next)
    {
      all_exits_near = false;
      break;
    }
  }

  if(entries.size()==1 && all_exits_near)
    return; // no, this loop is fine

  // The loop is not fine, we need to simulate.

  #if 0
  std::cout << "TRANSFORM: " <<
    entries.size() << " entries, " <<
    exits.size() << " exits." << std::endl;

    std::cout << "LOOP BEFORE TRANS:" << std::endl;
    output_loop(std::cout, program, begin, end);
  #endif

  const exprt loop_sym = get_new_variable();

  if(entries.size()>1)
    transform_entries(program, begin, end, loop_sym, entries);

  if(!all_exits_near)
    transform_exits(program, begin, end, loop_sym, exits);

  #if 0
    std::cout << "TRANSFORMED LOOP:" << std::endl;
    output_loop(std::cout, program, begin, end);
  #endif
}

/*******************************************************************\

Function: loop_transformt::check_loop_entries

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool loop_transformt::check_loop_entries(
  const goto_programt &program,
  goto_programt::const_targett begin,
  goto_programt::const_targett end)
{
  goto_programt::const_targett next_b=begin; next_b++;
  goto_programt::const_targett next_e=end; next_e++;

  for (goto_programt::const_targett i = next_b; i!=next_e; i++)
    forall_incoming_edges(i_it, i)    
    {
      unsigned from = (*i_it)->location_number;
      unsigned to = begin->location_number;
      if(!(from>=to))
      {
        str << "Warning: Multiple loop entries: " <<
          begin->location.get_file() << " " <<
          end->location.get_line();
        warning();
        return true;
      }
    }

  return false;
}



/*******************************************************************

 Function: loop_transformt::output_loop

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void loop_transformt::output_loop(
    std::ostream &out,
    const goto_programt &goto_program,
    goto_programt::const_targett begin,
    goto_programt::const_targett end)
{
  goto_programt::const_targett next = end; next++;

  for(goto_programt::const_targett it = begin;
      it!=next;
      it++)
    goto_program.output_instruction(namespacet(context), "", out, it);
}

/*******************************************************************

 Function: loop_transformt::run_check

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void loop_transformt::run_checks(
  const goto_programt &goto_program,
  goto_programt::const_targett begin,
  goto_programt::const_targett end)
{
  #if 0
  std::cout << "CHECKS: " << begin->function << " " << begin->location_number
    << " to " << end->location_number << std::endl;
  #endif

  check_loop_entries(goto_program, begin, end);
  check_loop_exits(goto_program, begin, end);
  check_loop_interleaved(goto_program, begin, end);

  assert(end->guard.is_true());
}

/*******************************************************************

 Function: transform_loops

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void transform_loops(
  goto_functionst &goto_functions,
  contextt &context,
  message_handlert &message_handler)
{
  loop_transformt loop_transform(context, message_handler);
  loop_transform.transform(goto_functions);
}

/*******************************************************************

 Function: transform_loops

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void transform_loops(
  goto_programt &goto_program,
  contextt &context,
  message_handlert &message_handler)
{
  loop_transformt loop_transform(context, message_handler);
  loop_transform.transform(goto_program);
}
