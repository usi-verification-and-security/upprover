/*******************************************************************\

Module: Main Module
Contributors: Daniel Kroening, CM Wintersteiger, Ondrej Sery,
                       Grigory Fedyukovich, Karine Even Mendoza,
                       Martin Blicha, Sepideh Asadi

\*******************************************************************/

#include <signal.h>
#include "parseoptions.h"
#include <iostream>

/*******************************************************************\

Function: main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int main(int argc, const char **argv)
{
  funfrog_parseoptionst parseoptions(argc, argv);
  int r = 0;
  try
  {
    r = parseoptions.main();
  }
  catch (const char* e)
  {
    std::cout << std::endl << "Caught exception: " << e << std::endl;
  }
  catch (const std::string &s)
  {
    std::cout << std::endl << "Caught exception: " << s << std::endl;
  }
  catch (const std::bad_alloc &e)
  {
    std::cout << std::endl << "MEMORY LIMIT EXCEEDED" << std::endl;
  }
  return r;
}
