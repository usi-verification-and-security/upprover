/*******************************************************************\
 
Module: GOTO-CC Main Module
 
Authors: Daniel Kroening, kroening@kroening.com
 
Date: May 2006
 
\*******************************************************************/

#include "cmdline_options.h"
#include "get_base_name.h"
#include "gcc_cmdline.h"
#include "ms_cl_cmdline.h"

/*******************************************************************\
 
Function: main
 
  Inputs:
 
 Outputs:
 
 Purpose:
 
\*******************************************************************/

int main(int argc, const char **argv)
{  
  if(argv==NULL || argc<1)
  {
    std::cerr << "failed to determine base name" << std::endl;
    return 1;
  }

  std::string base_name=get_base_name(argv[0]);

  if(base_name=="goto-link" || base_name=="link" ||
     base_name=="goto-cl" || base_name=="cl")
  {
    ms_cl_cmdlinet cmdline;
    cmdline_optionst cmdline_options(cmdline);
    cmdline_options.my_name=base_name;
    return cmdline_options.main(argc, argv);
  }
  else
  {
    gcc_cmdlinet cmdline;
    cmdline_optionst cmdline_options(cmdline);
    cmdline_options.my_name=base_name;
    return cmdline_options.main(argc, argv);
  }
}
