/*******************************************************************\

Module: Ranking Function Synthesis Base Class

Author: CM Wintersteiger

Date: September 2008

\*******************************************************************/

#include <sstream>

#include <std_expr.h>
#include <find_symbols.h>
#include <i2string.h>

#include <langapi/language_util.h>

#include "ranking_base.h"

/*******************************************************************\

 Function: ranking_synthesis_baset::print_dependencies

 Inputs:

 Outputs:

 Purpose:

 \********************************************************************/

std::string ranking_synthesis_baset::print_dependencies(const exprt &expr) const
{
  find_symbols_sett s;
  find_symbols(expr, s);

  std::stringstream str;

  str << "f(";
  for(find_symbols_sett::const_iterator it=s.begin();
      it!=s.end();
      it++)
  {
    if(it!=s.begin()) str << ", ";
    str << *it;
  }
  str << ")";

  return str.str();
}

/*******************************************************************\

Function: ranking_synthesis_baset::show_variables

  Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void ranking_synthesis_baset::show_variables(void)
{
  if(verbosity<9) return;
  std::string output;
      
  output = "IN: ";
  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
    output += it->second.as_string() + ", ";
  debug(output);

  output = "INTERMEDIATE: ";
  for(intermediate_statet::const_iterator it=intermediate_state.begin();
      it!=intermediate_state.end();
      it++)
    output += it->as_string() + ", ";
  debug(output);

  output = "OUTPUT MAP:\n";
  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
  {
    output +="  " + it->first.as_string() + " -> " + it->second.as_string() + "\n";
  }
  
  debug(output);
}

/*******************************************************************\

Function: ranking_synthesis_baset::show_varmap

  Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void ranking_synthesis_baset::show_varmap(
  const boolbvt &converter,
  std::ostream &out) const
{  
  out << "IN: " << std::endl;
  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
  {
    const irep_idt &ident = it->second;

    const symbolt &sym=ns.lookup(ident);
    out << from_expr(ns, "", symbol_exprt(it->second, sym.type)) << " = ";
    show_mapping(converter, ident, sym.type, out);
    out << std::endl;

//    value_variable_mapt::const_iterator fit=value_variable_map.find(it->second);
//    assert(fit!=value_variable_map.end());
//
//    const exprt vvar = fit->second;
//    out << "r(" << from_expr(it->second) << ")" << " = ";
//    show_mapping(converter, vvar.get("identifier"), vvar.type(), out);
//    out << std::endl;
  }

  out << "OUT: " << std::endl;
  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
  {
    const irep_idt &ident = it->first;
    const exprt &out_sym=symbol_exprt(ident, ns.lookup(ident).type);

    out << from_expr(ns, "", out_sym) << " = ";
    show_mapping(converter, ident, out_sym.type(), out);
    out << std::endl;

//    value_variable_mapt::const_iterator fit=value_variable_map.find(out_sym);
//    assert(fit!=value_variable_map.end());
//
//    const exprt vvar = fit->second;
//    out << "r(" << from_expr(out_sym) << ")" << " = ";
//    show_mapping(converter, vvar.get("identifier"), vvar.type(), out);
//    out << std::endl;
  }
}

/*******************************************************************\

Function: ranking_synthesis_baset::show_mapping

  Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void ranking_synthesis_baset::show_mapping(
  const boolbvt &converter,
  const irep_idt &ident,
  const typet &type,
  std::ostream &out) const
{
  symbol_exprt sym(ident, type);
  literalt l;

  if(type.id()=="bool" ||
     type.id()=="unsignedbv" ||
     type.id()=="signedbv" ||
     type.id()=="floatbv" ||
     type.id()=="fixedbv" ||
     type.id()=="bv" ||
     type.id()=="verilogbv")
  {
    unsigned width=bv_width(type);

    out << "[";
    for(unsigned i=width-1; i<width; i--)
    {
      if(converter.literal(sym, i, l))
        out << "N/A";
      else
      {
        if(l==const_literal(false))
          out << "F";
        else if(l==const_literal(true))
          out << "T";
        else
          out << i2string(l.dimacs());
      }

      if(i!=0) out << ",";
    }
    out << "]";
  }
  else
    out << "? (" << type << ")" << std::endl;
}

/*******************************************************************\

Function: ranking_synthesis_baset::find_intermediate_state

  Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void ranking_synthesis_baset::find_intermediate_state(void)
{
  find_symbols(body.body_relation, intermediate_state);
  find_nondet_symbols(body.body_relation, intermediate_state);

  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
  {
    intermediate_statet::iterator iit=intermediate_state.begin();
    for( ; iit!=intermediate_state.end(); iit++)
      if(*iit==it->first) { intermediate_state.erase(iit); break; }

    iit=intermediate_state.begin();
    for( ; iit!=intermediate_state.end(); iit++)
      if(*iit==it->second) { intermediate_state.erase(iit); break; }
  }
}

/*******************************************************************\

Function: ranking_synthesis_baset::find_largest_constant

  Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void ranking_synthesis_baset::find_largest_constant(const exprt &expr)
{
  if(expr.is_constant())
  {
    const std::string &value = expr.get("value").as_string();
    if(expr.type().id()!="integer") return;

    unsigned i;
    for(i=0; i<value.size(); i++)
      if(value[i]!='0') break;

    unsigned width=value.size()-i;

    if(width>largest_constant_width)
      largest_constant_width=width;


    mp_integer ival, lival;
    if(to_integer(expr, ival))
      throw "number conversion failed";

    if(to_integer(largest_constant, lival))
      throw "number conversion failed";

    if(ival>lival)
      largest_constant = expr;
  }
  else
    forall_operands(it, expr)
      find_largest_constant(*it);
}

/*******************************************************************\

Function: ranking_synthesis_baset::ranking

  Inputs:

 Outputs:

 Purpose:

\********************************************************************/

exprt ranking_synthesis_baset::ranking(void)
{
  find_symbols(body.body_relation, used_variables);
  find_intermediate_state();

  #if 1
  show_variables();
  #endif

  bool res=generate_functions();

  status(std::string("TConversion time: ") +
         time2string(conversion_time) + " sec.");
  status(std::string("TSolver time: ") +
         time2string(solver_time) + " sec.");
  status(std::string("TSolver calls: " + i2string(solver_calls)));

  if(!res)
    return nil_exprt();
  else
    return rank_relation;
}

/*******************************************************************\

Function: ranking_synthesis_baset::find_nondet_symbols

  Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void ranking_synthesis_baset::find_nondet_symbols(
  const exprt &expr,
  find_symbols_sett &set)
{
  if(expr.id()=="nondet_symbol")
  {
    const irep_idt &ident=expr.get("identifier");
    set.insert(ident);
    
    // make sure that there is a symbol for this,
    // so we can lookup the type later on.
    symbolt s;
    s.name=ident;
    s.type=expr.type();
    shadow_context.move(s);
  }
  else
    forall_operands(it, expr)
      find_nondet_symbols(*it, set);
}

/*******************************************************************\

 Function: ranking_synthesis_baset::cast_up

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void ranking_synthesis_baset::cast_up(exprt &a, exprt &b) const
{
  unsigned a_width=safe_width(a, ns);
  unsigned b_width=safe_width(b, ns);

  if(a.type().id()==b.type().id())
  {
    if(b_width==a_width)
      return;
    if(a_width>b_width)
    {
      typecast_exprt tc(a.type());
      tc.op() = b;
      b = tc;
    }
    else
    {
      typecast_exprt tc(b.type());
      tc.op() = a;
      a = tc;
    }
  }
  else
  {
    if(a.type().id()=="signedbv")
    {
      typet t = unsignedbv_typet(a_width);
      typecast_exprt tc(t);
      tc.op() = a;
      a = tc;
      cast_up(a, b);
    }
    else
    {
      assert(b.type().id()=="signedbv");
      typet t = unsignedbv_typet(b_width);
      typecast_exprt tc(t);
      tc.op() = b;
      b = tc;
      cast_up(a,b);
    }
  }

}
