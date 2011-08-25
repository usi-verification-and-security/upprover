/*******************************************************************\

Module: 

Author: Daniel Kroening

\*******************************************************************/

#ifdef _WIN32
#include <process.h>
#define getpid _getpid
#endif

#include <stdlib.h>

#ifdef __MACH__
#include <unistd.h>
#endif

#ifdef __linux__
#include <unistd.h>
#endif

#include "i2string.h"
#include "tempfile.h"

/*******************************************************************\

Function: get_temporary_file

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string get_temporary_file(const std::string &prefix, const std::string &suffix)
{
  return prefix+i2string(getpid())+suffix;
}

