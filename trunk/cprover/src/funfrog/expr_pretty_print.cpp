/*******************************************************************\

Module: Simple pretty printing visitor for exprt.


\*******************************************************************/
#ifdef DISABLE_OPTIMIZATIONS

#include "expr_pretty_print.h"

#include "utils/naming_helpers.h"
#include "utils/expressions_utils.h"

#include <sstream>

std::string 
expr_pretty_printt::addToDeclMap(const exprt &expr) 
{
    /* Exit if we don't save the prints for out stream in the end */
    if (partition_smt_decl == nullptr)
    {
        return "";
    }
    
    // Fix the type - SSA type => SMT type
    std::string type_expr = expr.type().id().c_str();
    type_expr[0] = static_cast<char>(std::toupper(type_expr[0]));
    if (type_expr == "Signedbv")
    {
        type_expr = SMTConstants::SMT_REAL;
        type_expr += " ";
    }
    
    // Fix Variable name - sometimes "nondet" name is missing, add it for these cases
    std::string name_expr = normalize_name(expr);
    if (is_cprover_rounding_mode_var(name_expr))
    {
        // We don't save __cprover built-ins
        return "";
    }
    
    // Create the output
    std::stringbuf code_buf;
    std::ostream out_code(&code_buf);
    out_code << SYMBOL_COLOR << "|" << name_expr.c_str() << "| () " << TYPE_COLOR << type_expr.c_str() << NORMAL_COLOR;
    std::string key = code_buf.str();
    
    // Insert the variable decl into a map of vars
    //std::cout << "** Debug ** " << key << std::endl;
    if (partition_smt_decl->find(key) == partition_smt_decl->end())
    {
        partition_smt_decl->insert(make_pair(key,expr));
    }
    
    // Return the clean expression name (SMT-LIB style)
    return name_expr;
}

double 
expr_pretty_printt::convertBinaryIntoDec(const exprt &expr) 
{
    // convert once per expt const - why? because if you "get" twice from the same object you don't get the same result
    if (isAlreadyConverted) 
    {
        isAlreadyConverted = false;
        return last_convered_value;
    }

    std::string test = print_number_2smt(expr);
    if (!test.empty())
    {
        return stod(test);
    }

    return 0;
}

void
expr_pretty_printt::operator()(const exprt &expr)
{
#ifdef DEBUG_SSA_SMT
	out << DEBUG_COLOR << "; EXPR OP " << expr.id() << NORMAL_COLOR << '\n';
#endif

    if (isTypeCast2Convert(expr)) { 
        // Take care of recurisve typecasting
        convertTypecast(expr);
    } else if (expr.id() == ID_symbol) {
        if (is_prev_token) out << " ";
        out << SYMBOL_COLOR << "|" << expr.get(ID_identifier) << "|" << NORMAL_COLOR;
#ifdef DEBUG_SSA_SMT_INFO
        if (!is_L2_SSA_symbol(expr)) {
            std::cerr << "\nWARNING: Using Symbol or L1 name instead of the L2 name in the SSA tree (" 
                    << expr.get(ID_identifier) << " : " << expr.type().id().c_str() << ")\n" ;
        }
#endif
        is_prev_token = true;
        addToDeclMap(expr); // Add the symbol to the symbol table
    } else if (expr.id() == ID_constant) {
        if (expr.is_boolean()) { // true or false
            out << CONSTANT_COLOR << expr.get(ID_value) << NORMAL_COLOR;
        } else {
            if (is_prev_token) out << " ";
            //convert = expr.get(ID_value).c_str();//add the value of Number to the characters in the stream
            out << CONSTANT_COLOR << convertBinaryIntoDec(expr) << NORMAL_COLOR;
            if (!last) {out << " "; is_prev_token = false;}
            else is_prev_token = true;
        }
    } else if (expr.id() == ID_nondet_symbol) {
        std::string name = addToDeclMap(expr); // Add the symbol to the symbol table
        if (is_prev_token) out << " ";
        out << OPERATOR_COLOR << "|" << (name.size() > 0 ? name : expr.get(ID_identifier)) << "|" << NORMAL_COLOR;
        is_prev_token = true;
    } else if (expr.id() == ID_notequal) {
        out << OPERATOR_COLOR << "not (=" << NORMAL_COLOR;
        out << " "; is_prev_token = false;
    } else if (expr.id() == ID_if) {
        out << OPERATOR_COLOR << "ite" << NORMAL_COLOR;
        out << " "; is_prev_token = false;
    } else {
        std::string checkOp = expr.id_string();
        if (checkOp.size() > 2) {
            if (checkOp.substr(0,5).compare("unary") == 0) {
                checkOp = "* " + checkOp.substr(5,1) + "1";
            }
        }
        out << OPERATOR_COLOR << checkOp << NORMAL_COLOR;
        out << " "; is_prev_token = false;
    }
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

/*******************************************************************
Main of SSA print
\*******************************************************************/
std::ostream&
expr_ssa_print(std::ostream& out, const exprt& expr, std::map <std::string,exprt>* partition_smt_decl,
		bool isNeg, bool contTerm)
{
  if (isNeg) out << "(not ";
  expr_pretty_printt pp(out,partition_smt_decl);

  pp.visit_SSA(expr);

  if (isNeg) out << ")";
  if (!contTerm) out << std::endl;

  return out;
}

std::ostream&
expr_ssa_print_smt_dbg(std::ostream& out, const exprt& expr, bool isNeg) {
	  if (isNeg) out << "(not ";

	  expr_pretty_printt pp(out);
	  pp.visit_SSA(expr);

	  if (isNeg) out << ")";

	  out << "\n";
	  return out;
}

std::ostream&
expr_ssa_print_guard(std::ostream& out, const exprt& expr, std::map <std::string,exprt>* partition_smt_decl)
{
  // Create the output
  std::ostream out_code(0);
  std::stringbuf code_buf;
  out_code.rdbuf(&code_buf);

  expr_pretty_printt pp(out_code,partition_smt_decl);
  pp.visit_SSA(expr); // get the expression

  // If not trivial add it to the output
  if (!expr.is_boolean())
	  out << "    " << code_buf.str() << (code_buf.str()).size() <<std::endl;

  return out;
}

/*******************************************************************
 Goal: takes CProver expression and creates SMT representation out of it without using OpenSMT,
 but employs string SMT-lib representation.
 This method is expected to mimic what we are exactly doing in the conversion (encoding):
 instead of using OPenSMT to convert to PTRefs,
 it manually converts exprs into SMTlib strings and dumps them.
 It does "Recursive inner order SSA representation"
\*******************************************************************/
void expr_pretty_printt::visit_SSA(const exprt& expr)
{
    bool isNegIn = false;
    if (expr.id() == ID_notequal) 
        isNegIn = true;
    
    if (isTypeCast2Convert(expr)) 
    { 
        convertTypecast(expr);
        if (isNegIn) out << ")"; /* Skip on that case the visit since changed typecast 0 to false */
    }
    else 
    {
        if (expr.has_operands()) {
            if (is_prev_token) 
                out << " ";
            
            out << "(";
            is_prev_token = true;
        }

        (*this)(expr);

        bool is_rdmd = isWithRoundingModel(expr); int i = 0; // If with rounding model and not BV then remove it
        last = false;
        forall_operands(it, expr) {
            if (is_rdmd) { // Divide with 3 operators
                if (i >= 2) {
                    // Skip - we don't need the rounding variable for non-bv logics
                } else {
                    if ((it == --expr.operands().end()) || (i ==1)) {
                        last = true;
                    }
                    this->visit_SSA(*it);
                    i++;
                }
            } else { // common regular case
                if (it == --expr.operands().end()) {
                  last = true;
                }
                this->visit_SSA(*it);
            }
        }

        // After all the expression parts printed
        if (isNegIn) out << ")";
        if (expr.has_operands()) {out << ")"; is_prev_token = true;}
    }

    last_convered_value = 0; isAlreadyConverted = false;
}

bool expr_pretty_printt::isWithRoundingModel(const exprt& expr) {
    // Check if for div op there is a rounding variable
    bool is_div_wtrounding = false;
    if (expr.id() == ID_floatbv_minus || expr.id() == ID_minus ||
        expr.id() == ID_floatbv_plus || expr.id() == ID_plus ||
        expr.id() == ID_floatbv_div || expr.id() == ID_div ||
        expr.id() == ID_floatbv_mult || expr.id() == ID_mult) {
        if ((expr.operands()).size() > 2)
            is_div_wtrounding = true; // need to take care differently!
    }
    // End of check - shall be on a procedure!
    return is_div_wtrounding;
}

bool expr_pretty_printt::isTypeCast2Convert(const exprt& expr)
{
    if (!expr.has_operands()) return false;
    
    return expr.id() == ID_typecast || expr.id() == ID_floatbv_typecast;
}

void expr_pretty_printt::convertTypecast(const exprt& expr)
{
    assert(!expr.operands().empty()); // Shall have symbol the type cast refers to
    
    // If more than that check why
    assert( ((expr.operands().size() == 1) && (expr.id() == ID_typecast))
            ||
            ((expr.operands().size() == 2) && (expr.id() == ID_floatbv_typecast))
          );

    if ((expr.operands())[0].is_constant()) {
        if (is_prev_token) out << " ";
        if (expr.is_boolean()) {
            if ((expr.operands())[0].is_zero()) {
                out << CONSTANT_COLOR << "false" << NORMAL_COLOR;
            } else {
                out << CONSTANT_COLOR << "true" << NORMAL_COLOR;
            }
        } else { /* Translate only if not boolean */
            double val_cast = convertBinaryIntoDec((expr.operands())[0]);
            last_convered_value = val_cast; isAlreadyConverted = true;
            out << CONSTANT_COLOR << val_cast << NORMAL_COLOR;
        }
        is_prev_token = true;
    } else {
        // GF: sometimes typecast is applied to variables, e.g.:
        //     (not (= (typecast |c::main::1::c!0#4|) -2147483648))
        //     in this case, we should replace it by the variable itself, i.e.:
        //     (not (= |c::main::1::c!0#4| -2147483648))
        // There is a whole expression in it!
        visit_SSA(expr.operands()[0]);
    }      
}
#endif
