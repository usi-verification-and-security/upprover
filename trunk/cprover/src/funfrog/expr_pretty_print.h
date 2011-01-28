/*******************************************************************\

Module: Simple pretty printing visitor for exprt.

Author: Ondrej Sery

\*******************************************************************/

#ifndef EXPR_PRETTY_PRINT_H
#define EXPR_PRETTY_PRINT_H

#include <expr.h>

class expr_pretty_printt
{
public:
  expr_pretty_printt(std::ostream& _out) : out(_out) {}

  virtual void operator()(const exprt &expr);

  void visit(const exprt& expr);

private:
  std::ostream& out;
  std::string indent;
  bool last;
};

void expr_pretty_print(std::ostream& out, const exprt& expr);

#endif
