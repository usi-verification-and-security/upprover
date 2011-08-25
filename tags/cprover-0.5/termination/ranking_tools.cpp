/*******************************************************************\

Module: Some tools for the termination/ranking engine

Author: CM Wintersteiger

Date: May 2009

\*******************************************************************/

#include <config.h>
#include <namespace.h>

#include <solvers/flattening/boolbv.h>

#include "ranking_tools.h"

/*******************************************************************\

Function: safe_width

  Inputs:

 Outputs:

 Purpose:

\********************************************************************/

unsigned safe_width(const exprt &e, const namespacet &ns)
{
  const typet &type=ns.follow(e.type());

  if(type.id()=="pointer" || type.id()=="reference")
    return config.ansi_c.pointer_width;
  
  return boolbv_widtht(ns)(type);
}


/*******************************************************************\

Function: tokenize

  Inputs: a string, a vector of tokens and a string of delimiters

 Outputs: nothing

 Purpose: fills the token vector with tokens separated by delimiters
          from the string

\*******************************************************************/

void tokenize(  const std::string& str,
                std::vector<std::string>& tokens,
                const std::string& delimiters)
{
    std::string::size_type lastPos = str.find_first_not_of(delimiters, 0);
    std::string::size_type pos     = str.find_first_of(delimiters, lastPos);

    while (std::string::npos != pos || std::string::npos != lastPos)
    {
        tokens.push_back(str.substr(lastPos, pos - lastPos));
        lastPos = str.find_first_not_of(delimiters, pos);
        pos = str.find_first_of(delimiters, lastPos);
    }
}
