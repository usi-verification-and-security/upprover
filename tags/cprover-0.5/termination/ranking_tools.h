/*******************************************************************\

Module: Some tools for the termination/ranking engine

Author: CM Wintersteiger

Date: May 2009

\*******************************************************************/

#ifndef RANKING_TOOLS_H_
#define RANKING_TOOLS_H_

#include <string>
#include <vector>

#include <expr.h>

unsigned safe_width(const exprt &e, const class namespacet &ns);

void tokenize(  const std::string& str,
                std::vector<std::string>& tokens,
                const std::string& delimiters = " ");


#endif /* RANKING_TOOLS_H_ */
