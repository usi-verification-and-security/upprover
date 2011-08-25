/*******************************************************************

 Module: Leaping GOTO Program

 Author: CM Wintersteiger

 \*******************************************************************/

#ifndef _CPROVER_LOOPFROG_LEAPING_GOTO_PROGRAM_H_
#define _CPROVER_LOOPFROG_LEAPING_GOTO_PROGRAM_H_

#include <goto-programs/goto_program.h>

class leaping_goto_programt:public goto_programt
{
public:
  std::ostream& output_instruction(
    const class namespacet &ns,
    const irep_idt &identifier,
    std::ostream& out,
    instructionst::const_iterator it) const;

  leaping_goto_programt() { }
};

#endif /*_CPROVER_LOOPFROG_LEAPING_GOTO_PROGRAM_H_*/
