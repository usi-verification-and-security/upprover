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

  void set_indent(unsigned _indent) {
    orig_indent = _indent;
    indent.assign(_indent, ' ');
  }
  
  void set_indent(const std::string& indent_str) {
    orig_indent = indent_str.length();
    indent = indent_str;
  }

private:
  std::ostream& out;
  std::string indent;
  unsigned orig_indent;
  bool last;
};

std::ostream& expr_pretty_print(std::ostream& out, const exprt& expr, 
        unsigned _indent = 0);

std::ostream& expr_pretty_print(std::ostream& out, const exprt& expr, 
        const std::string& indent_str);

#endif
