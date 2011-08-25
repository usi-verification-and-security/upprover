/*******************************************************************\

Module: Ranking Function Synthesis (SAT Enumeration)

Author: CM Wintersteiger

Date: October 2008

\*******************************************************************/

#include <memory>

#include <std_expr.h>
#include <arith_tools.h>
#include <simplify_expr.h>
#include <base_type.h>

#include <ansi-c/c_types.h>
#include <langapi/language_util.h>
#include <solvers/flattening/bv_pointers.h>

#include "rankfunction_typecheck.h"

#include "ranking_sat.h"

/********************************************************************\

 Function: ranking_synthesis_satt::instantiate

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

exprt ranking_synthesis_satt::instantiate(void)
{
  find_largest_constant(body.body_relation);

  binary_relation_exprt toplevel_and("and");

  toplevel_and.lhs() = body.body_relation; // that's R(x,x')

  exprt function;
  replace_mapt pre_replace_map;
      
  bool first=true;
  
  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
  {
    if(used_variables.find(it->first)==used_variables.end())
      continue;
    
    exprt var=symbol_exprt(it->first, ns.lookup(it->first).type);
    pre_replace_map[var] = // save the corresponding pre-var
            symbol_exprt(it->second, ns.lookup(it->second).type);
    
    adjust_type(var.type());
    const typet type=var.type();

    exprt coef=coefficient(var);    

    unsigned width=safe_width(var, ns);
    assert(width!=0);

    exprt term("*", typet(""));
    term.copy_to_operands(coef, var);

    if(first)
    {
      function=term;
      first=false;
    }
    else
    {
//      cast_up(function, term);
      exprt t("+", typet(""));
      t.move_to_operands(function, term);
      function = t;
    }
  }
  
  if(first) // non of the interesting variables was used - bail out!
  {
    debug("Completely non-deterministic template; "
           "this loop does not terminate.");
    return false_exprt();
  }

//  if(!largest_constant.is_zero())
//  {
//    // add the largest constant
//    symbol_exprt lc_sym("termination::LC", largest_constant.type());
//    exprt lc=largest_constant;
//    exprt lcc=coefficient(lc_sym);
////    cast_up(lc, lcc);
//    exprt m("*", typet(""));
//    m.move_to_operands(lcc, lc);
//
////    cast_up(function, m);
//    exprt t("+", typet(""));
//    t.move_to_operands(function, m);
//    function = t;
//  }

  // add a constant term
  symbol_exprt const_sym("termination::constant", signedbv_typet(2));
  exprt cc=coefficient(const_sym);

//  cast_up(function, cc);
  exprt t2("+", typet(""));
  t2.move_to_operands(function, cc);
  function=t2;
      
  contextt context;
  ansi_c_parse_treet pt;
  rankfunction_typecheckt typecheck(pt, context, ns, *message_handler);

  try
  {
    typecheck.typecheck_expr(function);
  }
  catch (...)
  {
    throw "TC ERROR";
  }
  

  exprt pre_function = function;
  replace_expr(pre_replace_map, pre_function);

  // save the relation for later
  rank_relation = binary_relation_exprt(function, "<", pre_function);
  
  // base_type(rank_relation, ns);

  toplevel_and.rhs()=not_exprt(rank_relation);

  return toplevel_and;
}

/*******************************************************************

 Function: ranking_synthesis_satt::generate_functions

 Inputs:

 Outputs:

 Purpose:

 \********************************************************************/

bool ranking_synthesis_satt::generate_functions(void)
{
  exprt templ = instantiate();

  if(body.variable_map.size()==0 || templ.is_false())
    return false;

  // some coefficient values
  c_valuest c_values;

  debug("Template:" + from_expr(ns, "", templ));

  satcheckt::resultt result=satcheckt::P_SATISFIABLE;

  while(result==satcheckt::P_SATISFIABLE)
  {
    if(c_values.size()==0)
      initialize_coefficients(c_values);
    else
    {
      if(increase_coefficients(c_values))
        break;
    }

    result=check_for_counterexample(templ, c_values,
                                    conversion_time, solver_time);
  }

  if(result==satcheckt::P_ERROR)
    throw ("Solver error.");
  else if(result==satcheckt::P_UNSATISFIABLE) // no counter-example
  {
    debug("Found ranking functions");

    // put the coefficient values in the rank relation
    replace_mapt replace_map;

    for(c_valuest::const_iterator it=c_values.begin();
        it!=c_values.end();
        it++)
    {
      replace_map[it->first] = from_integer(it->second, it->first.type());
    }

    replace_expr(replace_map, rank_relation);
    simplify(rank_relation, ns);

    return true;
  }
  else
    return false;
}

/*******************************************************************\

Function: ranking_synthesis_satt::initialize_coefficients

  Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void ranking_synthesis_satt::initialize_coefficients(c_valuest &c_values) const
{
  c_values.reserve(coefficient_map.size());

  // set all coefficients to -1
  for(coefficient_mapt::const_iterator it=coefficient_map.begin();
      it!=coefficient_map.end();
      it++)
  {
    if(it->first.type().id()=="bool")
      c_values.push_back(std::pair<exprt, int>(it->second,0));
    else
      c_values.push_back(std::pair<exprt, int>(it->second,-1));
  }
}

/*******************************************************************\

Function: ranking_synthesis_satt::increase_coefficients

  Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool ranking_synthesis_satt::increase_coefficients(c_valuest &c_values) const
{
  for(c_valuest::reverse_iterator it=c_values.rbegin();
      it!=c_values.rend();
      it++)
  {
    if(it->second>=-1 && it->second<1)
    {
      it->second++;
      return false;
    }
    else
    {
      if(it->first.type().id()=="bool")
        it->second=0;
      else
        it->second=-1;
    }
  }

  return c_values.size()>0;
}

/*******************************************************************\

Function: ranking_synthesis_satt::show_coefficients

  Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void ranking_synthesis_satt::show_coefficients(c_valuest &c_values)
{
  if(verbosity<9) return;
  
  std::string t("Coefficients: ");
  for(c_valuest::const_iterator it=c_values.begin();
      it!=c_values.end();
      it++)
  {
    if(it!=c_values.begin()) t+=", ";
    t+=from_expr(ns, "", it->first) +"=" +
      from_expr(ns, "", from_integer(it->second, it->first.type()));
  }
  
  debug(t);
}

/*******************************************************************\

Function: ranking_synthesis_satt::show_counterexample

  Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void ranking_synthesis_satt::show_counterexample(boolbvt &converter)
{  
  if(verbosity<9) return;
  std::string output=" ... NO: ";
  
  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
  {
    if(used_variables.find(it->first)==used_variables.end())
      continue;
    
    if(it!=body.variable_map.begin()) output += ", ";

    exprt postsym=symbol_exprt(it->first, ns.lookup(it->first).type);
    exprt presym=symbol_exprt(it->second, ns.lookup(it->second).type);
    
    exprt post=converter.get(postsym);
    
    if(post.id()!="nil")
    {
     output += from_expr(ns, "", postsym) + "=" + from_expr(ns, "", post) + " (";
    }
    else
     output += "? (";

    exprt pre=converter.get(presym);
    if(pre.id()!="nil")
      output += from_expr(ns, "", pre);
    else
      output += "?";

    output += ")";
  }

  debug(output);
}

/*******************************************************************\

Function: ranking_synthesis_satt::check_for_counterexample

  Inputs:

 Outputs:

 Purpose:

\********************************************************************/

satcheckt::resultt ranking_synthesis_satt::check_for_counterexample(
   const exprt &templ,
   c_valuest &c_values,
   fine_timet &conversion_time,
   fine_timet &solver_time)
{
  satcheckt::resultt result;

  satcheckt solver;
  bv_pointerst converter(ns, solver);   

  solver.set_message_handler(get_message_handler());
  solver.set_verbosity(verbosity);
  converter.set_message_handler(get_message_handler());
  converter.set_verbosity(verbosity);

  show_coefficients(c_values);

  fine_timet before = current_time();
  converter.set_to_true(templ);

  for(c_valuest::const_iterator it=c_values.begin();
      it!=c_values.end();
      it++)
  {
    equality_exprt eq;

    if(it->first.get("identifier")=="termination::constant$C")
    {
      mp_integer cval;
      if(to_integer(largest_constant, cval))
        throw "number conversion failed";

      mp_integer b=cval * it->second;

      eq=equality_exprt(it->first,
                        from_integer(b, it->first.type()));
    }
    else
      eq=equality_exprt(it->first, from_integer(it->second, it->first.type()));

    converter.set_to_true(eq);
  }

  conversion_time+=current_time()-before;

  before = current_time();
  result=solver.prop_solve();
  solver_time+=current_time()-before;
  solver_calls++;

  std::string output;
  
  if(result==satcheckt::P_SATISFIABLE)    
    show_counterexample(converter);
  else if(result==satcheckt::P_UNSATISFIABLE)
    output += " ... YES!\n";
  else
    output += "ERROR\n";
  
  debug(output);

  return result;
}

/*******************************************************************\

 Function: ranking_synthesis_satt::coefficient

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

exprt ranking_synthesis_satt::coefficient(const exprt &expr)
{
  assert(expr.id()=="symbol");

  exprt &entry = coefficient_map[expr];

  if(entry==exprt())
  {
    irep_idt ident=expr.get("identifier").as_string() + "$C";

    // set up a new coefficient
    entry.id("symbol");
    entry.set("identifier", ident);

    // adjust the coefficient type
    entry.type()=signedbv_typet(2); //expr.type();
  }

  return entry;
}

/*******************************************************************\

 Function: ranking_synthesis_satt::adjust_type

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void ranking_synthesis_satt::adjust_type(typet &type) const
{
  if(type.id()=="bool")
  {
    type=uint_type();
    type.set("width", 1);
  }
}
