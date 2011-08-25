/*******************************************************************

 Module: Conditional Copies of a GOTO Programs

 Author: CM Wintersteiger

\*******************************************************************/

#include "conditional_goto_copy.h"


void conditional_goto_copy(
  const goto_programt &src,
  goto_programt &dest,
  goto_programt::const_targett &last)
{
  // Definitions for mapping between the two programs
  typedef std::map<goto_programt::const_targett, 
                   goto_programt::targett> targets_mappingt;
  targets_mappingt targets_mapping;

  dest.clear();

  // Loop over program - 1st time collects targets and copy
  
  goto_programt::const_targett onemore = last; onemore++;
  for(goto_programt::const_targett it=src.instructions.begin();
      it!=onemore;
      it++)
  {
    goto_programt::targett new_instruction=dest.add_instruction();
    targets_mapping[it]=new_instruction;
    *new_instruction=*it;
  }
  
  // Loop over program - 2nd time updates goto targets
  
  for(goto_programt::targett it=dest.instructions.begin();
      it!=dest.instructions.end();
      it++)
  {
    if(it->is_goto() || it->is_start_thread())
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
          it->guard.make_not();
          it->type = ASSUME;
          it->labels.push_back("restricted goto");
          break;
        }
        else
        {
          *t_it=m_target_it->second;
        }
      }
    }
  }

  dest.update();
}
