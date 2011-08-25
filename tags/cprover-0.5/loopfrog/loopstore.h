/*******************************************************************

 Module: Loop Storage

 Author: CM Wintersteiger

\*******************************************************************/

#ifndef _CPROVER_LOOPFROG_LOOPSTORE_H_
#define _CPROVER_LOOPFROG_LOOPSTORE_H_

#include <map>
#include <goto-programs/goto_program.h>

class loopstoret : 
  public std::map<unsigned, goto_programt>
{
private:
public:
  loopstoret(void) :
    std::map<unsigned, goto_programt>()
    {};
};

#endif /*_CPROVER_LOOPFROG_LOOPSTORE_H_*/
