/*******************************************************************\

Module: Simple pretty printing visitor for exprt.

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_EXPR_PRETTY_PRINT_H
#define CPROVER_EXPR_PRETTY_PRINT_H
#ifdef DISABLE_OPTIMIZATIONS
#include <expr.h>

class expr_pretty_printt
{
public:
    expr_pretty_printt(std::ostream &_out) : expr_pretty_printt(_out, nullptr) {}

    expr_pretty_printt(std::ostream &_out, std::map<std::string, exprt> *partition_smt_decl)
      : out(_out), is_prev_token(false), orig_indent(0), last(false), partition_smt_decl(partition_smt_decl),
        isAlreadyConverted(false), terminal_color(false)
        {
            if(terminal_color)
            {
              EDGE_COLOR = "\033[2;31m";
              TYPE_COLOR = "\033[0;35m"; //Magenta purple
              CONSTANT_COLOR = "\033[0;36m"; //cyan
              SYMBOL_COLOR = "\033[0m";
              OPERATOR_COLOR = "\033[1;32m"; //green
              NORMAL_COLOR = "\033[0m";
              DEBUG_COLOR = "\0[34m";
            }
        }

    virtual ~expr_pretty_printt() { partition_smt_decl = nullptr; } // to assure nothing will happen to the map
    virtual void operator()(const exprt &expr);

    void visit(const exprt &expr);

    void visit_SSA(const exprt &expr);

    void set_indent(unsigned _indent) {
        orig_indent = _indent;
        indent.assign(_indent, ' ');
    }

    void set_indent(const std::string &indent_str) {
        orig_indent = indent_str.length();
        indent = indent_str;
    }
    
private:
    std::ostream &out;
    bool is_prev_token; // is token or space
    std::string indent;
    unsigned int orig_indent;
    bool last;

    std::map<std::string, exprt> *partition_smt_decl;

    std::string addToDeclMap(const exprt &expr);

    double convertBinaryIntoDec(const exprt &expr);

    bool isWithRoundingModel(const exprt &expr);

    bool isTypeCast2Convert(const exprt &expr);

    void convertTypecast(const exprt &expr);

    // Can do it only because refer to const!!
    bool isAlreadyConverted;
    double last_convered_value;
    
    //to print colored text (e.g, in SSA-form) set to true in C'tor
    bool  terminal_color;
    
    std::string EDGE_COLOR;
    std::string TYPE_COLOR;
    std::string  CONSTANT_COLOR;
    std::string  SYMBOL_COLOR;
    std::string  OPERATOR_COLOR;
    std::string  NORMAL_COLOR;
    std::string  DEBUG_COLOR;
};

std::ostream &expr_pretty_print(std::ostream &out, const exprt &expr,
                                unsigned _indent = 0);

std::ostream &expr_ssa_print_smt_dbg(std::ostream &out,
                                     const exprt &expr, bool isNeg);

std::ostream &expr_ssa_print(std::ostream &out, const exprt &expr,
                             std::map<std::string, exprt> *partition_smt_decl,
                             bool isNeg, bool contTerm = false);

std::ostream &expr_pretty_print(std::ostream &out, const exprt &expr,
                                const std::string &indent_str);

std::ostream &expr_ssa_print_guard(std::ostream &out, const exprt &expr,
                                   std::map<std::string, exprt> *partition_smt_decl);

#endif
#endif
