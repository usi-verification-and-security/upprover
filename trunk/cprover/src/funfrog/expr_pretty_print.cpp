/*******************************************************************\

Module: Simple pretty printing visitor for exprt.

Author: Ondrej Sery

\*******************************************************************/

#include "expr_pretty_print.h"
#include "format_constant.h"

#define EDGE_COLOR "\033[2;37m"
#define TYPE_COLOR "\033[0;37m"
#define CONSTANT_COLOR "\033[0;36m"
#define SYMBOL_COLOR "\033[0m"
#define OPERATOR_COLOR "\033[1;32m"
#define NORMAL_COLOR "\033[0m"

void
expr_pretty_printt::operator()(const exprt &expr)
{
  out << EDGE_COLOR << indent << NORMAL_COLOR;
  if (expr.id() == ID_symbol) {

    out << SYMBOL_COLOR << expr.get(ID_identifier) << TYPE_COLOR
      << " (" << expr.type().id() << ")" << NORMAL_COLOR;

  } else if (expr.id() == ID_constant) {

    out << CONSTANT_COLOR << expr.get(ID_value) << NORMAL_COLOR;

  } else {

    out << OPERATOR_COLOR << expr.id() << NORMAL_COLOR;

  }
  out << std::endl;
}

void
expr_pretty_printt::visit(const exprt& expr) {
  std::string old_indent = indent;

  (*this)(expr);

  if (indent.length() > orig_indent + 1) {
    indent = indent.substr(0, indent.length()-2) + 
            (last ? "  +-" : "| +-");
  } else indent += "+-";

  last = false;
  forall_operands(it, expr) {
    if (it == --expr.operands().end()) {
      last = true;
    }
    this->visit(*it);
  }
  indent = old_indent;
}

std::ostream&
expr_pretty_print(std::ostream& out, const exprt& expr, unsigned _indent)
{
  expr_pretty_printt pp(out);

  if (_indent > 0)
    pp.set_indent(_indent);
  pp.visit(expr);
  
  return out;
}


std::ostream&
expr_pretty_print(std::ostream& out, const exprt& expr, 
        const std::string& indent_str)
{
  expr_pretty_printt pp(out);

  pp.set_indent(indent_str);
  pp.visit(expr);
  
  return out;
}
