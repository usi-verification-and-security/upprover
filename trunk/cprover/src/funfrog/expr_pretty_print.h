/*******************************************************************\

Module: Simple pretty printing visitor for exprt.

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_EXPR_PRETTY_PRINT_H
#define CPROVER_EXPR_PRETTY_PRINT_H

#include <expr.h>

class expr_pretty_printt
{
public:
  expr_pretty_printt(std::ostream& _out) : out(_out) { }

  virtual void operator()(const exprt &expr);

  void visit(const exprt& expr);

  void set_indent(int _indent) {
    indent.assign(_indent, ' ');
  }

private:
  std::ostream& out;
  std::string indent;
  bool last;
};

void expr_pretty_print(std::ostream& out, const exprt& expr, int _indent = 0);

#endif
