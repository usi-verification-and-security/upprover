/*******************************************************************\

Module: Entry point for UpProver
Contributors: Grigory Fedyukovich, Martin Blicha, Sepideh Asadi

\*******************************************************************/

#include <signal.h>
#include "parser_upprover.h"
#include <iostream>

/*******************************************************************\

Function: main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int main(int argc, const char **argv)
{
    parser_upprovert parser_upp(argc, argv);
    int r = 0;
    try
    {
        r = parser_upp.main();
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
