/*******************************************************************\

Module: Custom Program Compression

Author: CM Wintersteiger

\*******************************************************************/

#include <goto-programs/remove_skip.h>
#include <goto-programs/slicer.h>
#include <simplify_expr.h>
#include <find_symbols.h>

#include "string_utils.h"

#include "program_compression.h"

/*******************************************************************\

Function: compress_program

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void compress_program(goto_programt &program)
{
  #if 0
  std::cout << "COMPRESS_PROGRAM" << std::endl;
  #endif
  
  for(goto_programt::instructionst::iterator it = 
        program.instructions.begin();
      it!=program.instructions.end();
      it++)
  {
    if(it->type==GOTO)
    { 
      if(it->guard.is_false())
        it->make_skip();
      else 
      {
        goto_programt::const_targett next = it; next++;
        
        if(it->targets.front()==next) // this goto is really useless.
          it->make_skip();
      }
    }
    else if(it->type==OTHER && it->code.get("statement")=="decl")
      it->make_skip();
  }
    
  remove_skip(program);
  program.update();
}
