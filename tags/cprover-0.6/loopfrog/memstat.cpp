/*******************************************************************

 Module: Some memory statistics

 Author: CM Wintersteiger

\*******************************************************************/

#ifdef linux
#include <malloc.h>
#endif

#include "memstat.h"

unsigned long current_memory(void)
{
  #ifdef __linux__
    static struct mallinfo l_mallinfo ;
    static unsigned long l;
    
    l_mallinfo = mallinfo();
    l = l_mallinfo.uordblks + l_mallinfo.hblkhd;    
    
    return l;
  #else
    // TODO: Mac?
  #endif
}
