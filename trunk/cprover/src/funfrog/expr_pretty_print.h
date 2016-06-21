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
  expr_pretty_printt(std::ostream& _out)
	: out(_out), is_prev_token(false), partition_smt_decl(0), orig_indent(0), last(false), isAlreadyConverted(false) { }
  expr_pretty_printt(std::ostream& _out, std::map <std::string,exprt>* partition_smt_decl)
  	  : out(_out), is_prev_token(false), partition_smt_decl(partition_smt_decl), orig_indent(0), last(false), isAlreadyConverted(false) { }

  virtual ~expr_pretty_printt() { partition_smt_decl = NULL; } // to assure nothing will happen to the map
  virtual void operator()(const exprt &expr);

  void visit(const exprt& expr);
  void visit_SSA(const exprt& expr);

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
  bool is_prev_token; // is token or space
  std::map <std::string,exprt>* partition_smt_decl;

  std::string addToDeclMap(const exprt &expr);
  long convertBinaryIntoDec(const exprt &expr);

  // Can do it only because refer to const!!
  bool isAlreadyConverted;
  long last_convered_value;
};

std::ostream& expr_pretty_print(std::ostream& out, const exprt& expr, 
        unsigned _indent = 0);

std::ostream& expr_ssa_print(std::ostream& out, const exprt& expr,
		std::map <std::string,exprt>* partition_smt_decl,
		bool isNeg, bool contTerm=false);

std::ostream& expr_pretty_print(std::ostream& out, const exprt& expr, 
        const std::string& indent_str);

std::ostream& expr_ssa_print_guard(std::ostream& out, const exprt& expr,
		std::map <std::string,exprt>* partition_smt_decl);

#endif
