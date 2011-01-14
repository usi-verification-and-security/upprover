/*******************************************************************\

Module: 

Author: CM Wintersteiger

\*******************************************************************/

#ifndef EXPR2SENESCHAL_H_
#define EXPR2SENESCHAL_H_

#include <util/expr.h>
#include <util/namespace.h>

class expr2seneschalt
{
protected:
  const namespacet &ns;
 
public:
  expr2seneschalt(const namespacet &_ns) : ns(_ns) {}
  ~expr2seneschalt() {}

  class UnhandledException
  {
  public:
    exprt reason;
    UnhandledException(exprt r) : reason(r) {};
  };

  std::string convert(const exprt &e, 
                      bool negated=false, 
                      bool bool_context=false);
};

#endif
