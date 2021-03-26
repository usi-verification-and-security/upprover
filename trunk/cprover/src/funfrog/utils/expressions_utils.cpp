//
// Created by Martin Blicha on 24.08.18.
//

#include "expressions_utils.h"

#include <rational.h>
#include <rational_tools.h>
#include <arith_tools.h>
#include <fixedbv.h>
#include <ieee_float.h>

void getVarsInExpr(exprt & e, std::set<exprt> & vars) {
    if (e.id() == ID_symbol) {
        if (is_cprover_builtins_var(e)) {
            // Skip rounding_mode or any other builtins vars
        } else {
            vars.insert(e);
        }
    } else if (e.has_operands()) {
        for (unsigned int i = 0; i < e.operands().size(); i++) {
            getVarsInExpr(e.operands()[i], vars);
        }
    }
}


/*******************************************************************\

Function: create_bound_string

 Inputs: 

 Outputs: 

 Purpose: for type constraints of CUF and LRA
 * Was part of smtcheck_opensmt2t originally

\*******************************************************************/
std::string create_bound_string(std::string base, int exp)
{
    std::string ret = base;
    int size = exp - base.size() + 1; // for format 3.444444
    for (int i=0; i<size;i++)
        ret+= "0";

    return ret;
}

// Check if the expression is a linear operator
bool is_linear_expression(const exprt &expr) {
    // Must be true
    if (!expr.has_operands()) return true;
    if (expr.operands().size() < 2) return true;
    if (expr.operands()[0].is_constant()) return true;
    if (expr.operands()[1].is_constant()) return true;
    
    const irep_idt & _id = expr.id();
    if(_id == ID_mult) return false;
    if(_id == ID_div) return false;
    if(_id == ID_floatbv_mult) return false;
    if(_id == ID_floatbv_div) return false;
    
    return true; // unknown
}

// inspired from expr2ct::convert_constant
const std::string print_number_2smt(const exprt &expr)
{
    if(expr.is_constant())
    {
        const std::string &value=expr.get_string(ID_value);
        const irep_idt &type_id=expr.type().id_string();

        if(type_id==ID_integer || type_id==ID_natural)
        {
            mp_integer int_value=string2integer(value);
            return integer2string(int_value);
        }
        else if(type_id==ID_c_enum || type_id==ID_c_enum_tag)
        {
            const irep_idt helper_id= // Taken from cprover expr2.cpp
                type_id==ID_c_enum
                ?to_c_enum_type(expr.type()).subtype().id()
                :to_c_enum_tag_type(expr.type()).subtype().id();

            mp_integer int_value=binary2integer(id2string(expr.get_string(ID_value))
                , helper_id==ID_signedbv);

            return integer2string(int_value);
        }
        else if(type_id==ID_rational)
        {
            std::stringstream convert; // stringstream used for the conversion
            convert.precision(1);
            rationalt rat_value;
            if(to_rational(expr, rat_value)) assert(false);
            convert << rat_value;
            return convert.str();
        }
        else if (type_id==ID_unsignedbv ||
                 type_id==ID_signedbv ||
                 type_id==ID_c_bit_field ||
                 type_id==ID_c_bool)
        { // from expr2c.cpp code
//            mp_integer int_value=binary2integer(id2string(value),
//                                                type_id==ID_signedbv);
            const constant_exprt src = to_constant_expr(expr);
            const typet &type = src.type();
            const auto width = to_bitvector_type(type).get_width();
            mp_integer int_value = bvrep2integer(value, width, type.id() == ID_signedbv);
            return integer2string(int_value);
        }
        else if (expr.is_boolean())
        {
            if (expr.is_true() || expr.is_one())
                return "1";
            else if (expr.is_false() || expr.is_zero())
                return "0";
            else
                return "";
        }
        else
        {
            if (expr.is_zero()) return "0";
            if (expr.is_one()) return "1";

            // Else try to extract the number
            std::string temp_try1(expr.get(ID_C_member_name).c_str()); // KE: need testing!
            if (temp_try1.size() > 0)
            {
                // WIll get here only for positive numbers, the rest will try differently
                return temp_try1;
            }
            else if(type_id==ID_fixedbv)
            {
                return (fixedbvt(to_constant_expr(expr))).to_ansi_c_string();
            }
            else if(type_id==ID_floatbv)
            {
                ieee_floatt temp = ieee_floatt(to_constant_expr(expr));
                std::string ans_cand = temp.to_ansi_c_string();
                if (ans_cand.find("e+") != std::string::npos)
                    return temp.to_string_decimal(ans_cand.size());
                if (ans_cand.find("e-") != std::string::npos)
                    return temp.to_string_decimal(ans_cand.size());
                if (ans_cand != "0.000000" && ans_cand != "-0.000000" && ans_cand != "0" && ans_cand != "-0") {
                    return ans_cand; // If the translation makes sense - returns it
                } else { // Else try to get something closer.
                    double temp_double = temp.to_double(); if (temp_double == 0) return "0";
                    return std::to_string(temp_double);
                }
            }
        }
    }

    return "";
}

