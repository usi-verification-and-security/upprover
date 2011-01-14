/*******************************************************************\

Module: Ranking Function Synthesis (QBF Coefficient Synthesis)

Author: CM Wintersteiger

Date: October 2008

\*******************************************************************/

#include <memory>

#include <std_expr.h>
#include <arith_tools.h>
#include <simplify_expr.h>
#include <i2string.h>
#include <prefix.h>
#include <base_type.h>

#include <ansi-c/c_types.h>

#include <langapi/language_util.h>

#ifdef HAVE_QBF_CORE
#include <solvers/qbf/qbf_core.h>
#include <solvers/qbf/qbf_squolem_core.h>
#include <solvers/qbf/qbf_bdd_core.h>
#include <solvers/qbf/qbf_skizzo_core.h>
#include <solvers/qbf/qbf_qube_core.h>
#endif

#include <solvers/flattening/bv_pointers.h>

#include "rankfunction_typecheck.h"

#include "ranking_qbf.h"

#define CONSTANT_COEFFICIENT_ID "termination::constant"

/*******************************************************************\

Function: ranking_synthesis_qbft::quantify_variables

  Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void ranking_synthesis_qbft::quantify_variables(
  boolbvt &converter,
  qdimacs_coret &solver)
{
  // first quantify all coefficients; those have to be constants
  for(coefficient_mapt::const_iterator it=coefficient_map.begin();
      it!=coefficient_map.end();
      it++)
  {
    const exprt &c = it->second;

    const exprt *sym=&c;
    while(sym->id()=="typecast")
      sym=&sym->op0();

    quantify_variable(converter, solver, *sym, false);
  }

  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
  {
    if(used_variables.find(it->first)==used_variables.end())
      continue;
    
    const exprt pre=symbol_exprt(it->second, ns.lookup(it->second).type);

    #if 0
    std::cout << "Quantifying " << from_expr(pre) << " (" <<
      from_expr(post) << ")" << std::endl;
    #endif

    quantify_variable(converter, solver, pre, true); // x
  }

  for(intermediate_statet::const_iterator it=intermediate_state.begin();
      it!=intermediate_state.end();
      it++)
  {
    if(used_variables.find(*it)==used_variables.end())
      continue;
    
    bool is_nondet=has_prefix(it->as_string(), "symex::nondet");
    irep_idt orig_ident;    
    exprt sym;
    
    if(is_nondet)
    {
      orig_ident=*it;
      sym=symbol_exprt(*it, ns.lookup(orig_ident).type);
      sym.id("nondet_symbol");
    }
    else
    {
      orig_ident=(it->as_string().substr(0, it->as_string().rfind('@')));
      orig_ident=(orig_ident.as_string().substr(0, orig_ident.as_string().rfind('#')));
      sym=symbol_exprt(*it, ns.lookup(orig_ident).type);
    }
        
    quantify_variable(converter, solver, sym, true);
  }

  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
  {
    if(used_variables.find(it->first)==used_variables.end())
      continue;

    const exprt post=symbol_exprt(it->first, ns.lookup(it->first).type);

    // we assume that x' is determined by R(x,x')
    quantify_variable(converter, solver, post, true); // x'
  }
}

/*******************************************************************\

Function: ranking_synthesis_qbft::quantify_variable

  Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void ranking_synthesis_qbft::quantify_variable(
    boolbvt &converter,
    qdimacs_coret &solver,
    const exprt &sym_in,
    bool universal)
{
  exprt sym=sym_in;
  //base_type(sym, ns);
  
  #if 1
  std::cout << ((universal)?"FORALL ":"EXISTS ") << from_expr(ns, "", sym) << " ";
  #endif
  literalt l;
  
  // first convert it; this does not add clauses
  bvt bv; converter.convert_bv(sym, bv);

  #if 0
  std::cout << "BV sym: " << sym << std::endl;
  std::cout << "BV: ";
  for(bvt::const_iterator it=bv.begin(); it!=bv.end(); it++)
    std::cout << it->dimacs() << ", ";
  std::cout << std::endl;
  #endif

  unsigned width=safe_width(sym, ns);

  for(unsigned i=0; i<width; i++)
  {
    if(!converter.literal(sym, i, l))
    {
      assert(l.var_no()!=0);
      quantify_innermost(solver, l.var_no(), universal);
      solver.variable_map[l.var_no()] = qdimacs_coret::symbol_mapt(sym, i);
    }
  }
}

/*******************************************************************\

Function: ranking_synthesis_qbft::quantify_innermost

  Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool ranking_synthesis_qbft::quantify_innermost(
  qdimacs_coret &solver,
  unsigned var_no,
  bool universal) const
{
  literalt l(var_no, false);

  if(!l.is_constant())
  {
    if(universal)
      solver.set_quantifier(qdimacs_cnft::quantifiert::UNIVERSAL, l);
    else
      solver.set_quantifier(qdimacs_cnft::quantifiert::EXISTENTIAL, l);
  }

  return true;
}

/********************************************************************\

 Function: ranking_synthesis_qbft::instantiate_template

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

exprt ranking_synthesis_qbft::instantiate(void)
{
  find_largest_constant(body.body_relation);

  #if 0
  std::cout << "Largest constant width: " << largest_constant_width << std::endl;
  #endif

  binary_relation_exprt implication("=>");
  implication.lhs() = body.body_relation; // that's R(x,x')

  exprt poly=instantiate_polynomial();  
  
  if(constrain_mode==COEFFICIENTS_UNCONSTRAINED)
    implication.rhs() = poly;
  else // COEFFICIENTS_CONSTRAINED
  {
    and_exprt constraints;
    
    for(coefficient_mapt::const_iterator it=coefficient_map.begin();
        it!=coefficient_map.end();
        it++)
    {
      constraints.copy_to_operands(
        or_exprt(
          binary_relation_exprt(it->second, ">=", from_integer(-1, it->second.type())),
          binary_relation_exprt(it->second, "<=", from_integer(+1, it->second.type()))
        )
      );
    }
  
    implication.rhs() = and_exprt(poly, constraints);
  }

  // save the relation for later
  rank_relation = implication.rhs();

  return implication;
}

/********************************************************************\

 Function: ranking_synthesis_qbft::instantiate_polynomial

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

exprt ranking_synthesis_qbft::instantiate_polynomial(void)
{
  exprt function;
  replace_mapt pre_replace_map;

  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
  {
    if(used_variables.find(it->first)==used_variables.end())
      continue;
    
    exprt var=symbol_exprt(it->first, ns.lookup(it->first).type);
    pre_replace_map[var] =  // save the corresponding pre-var
        symbol_exprt(it->second, ns.lookup(it->second).type);
    
//    const typet &type=var.type();
    adjust_type(var.type());

    exprt coef=coefficient(var);

    exprt term("*", typet(""));
    term.copy_to_operands(coef, var);

    if(it==body.variable_map.begin())
      function=term;
    else
    {
//      cast_up(function, term);
      exprt t("+", typet(""));
      t.move_to_operands(function, term);
      function = t;
    }
  }


//  if(!largest_constant.is_zero())
//  {
//    // add the largest constant
//    symbol_exprt lc_sym("termination::LC", largest_constant.type());
//    exprt lc=largest_constant;
//    exprt lcc=coefficient(lc_sym, safe_width(lc_sym));
//    cast_up(lc, lcc);
//    exprt m("*", lcc.type());
//    m.move_to_operands(lcc, lc);
//
//    cast_up(function, m);
//    exprt t("+", function.type());
//    t.move_to_operands(function, m);
//    function = t;
//  }

  // add a constant term
  symbol_exprt const_sym("termination::constant", signedbv_typet(32));
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

  return binary_relation_exprt(function, "<", pre_function);
}

/*******************************************************************\

 Function: ranking_synthesis_qbft::coefficient

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

exprt ranking_synthesis_qbft::coefficient(const exprt &expr)
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
    if(constrain_mode==COEFFICIENTS_CONSTRAINED)
      entry.type()=signedbv_typet(2); //expr.type();
    else
      entry.type()=signedbv_typet(safe_width(expr, ns)); //expr.type();

    assert(expr.type().id()=="signedbv" ||
           expr.type().id()=="unsignedbv" ||
           expr.type().id()=="bool");

//    if(entry.type()!=expr.type())
//    {
//      typecast_exprt tc(expr.type());
//      tc.op() = entry;
//      entry = tc;
//    }
  }

  return entry;
}

/*******************************************************************\

 Function: ranking_synthesis_qbft::generate_functions

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool ranking_synthesis_qbft::generate_functions(void)
{
  #if 0
  std::cout << "GENERATE: " << templ << std::endl;
  #endif

  std::auto_ptr<qdimacs_coret> solver(choose_qbf_core_extractor());
  bv_pointerst converter(ns, *solver);

  solver->set_verbosity(get_verbosity());
  solver->set_message_handler(get_message_handler());
  converter.set_verbosity(get_verbosity());
  converter.set_message_handler(get_message_handler());

  exprt t=instantiate();

  status("Template:");
  quantify_variables(converter, *solver);

  std::cout << std::endl << from_expr(ns, "", t) << std::endl;

  status("Converting template...");
  fine_timet before = current_time();
  converter.set_to_true(t);
  conversion_time += current_time()-before;

  if(get_verbosity()>5)
      show_varmap(converter, std::cout);

  status("Solving...");
  before = current_time();
  qdimacs_coret::resultt res = solver->prop_solve();
  solver_time += current_time()-before;
  solver_calls++;

  if(res==qdimacs_coret::P_SATISFIABLE)
  {
    status("Found ranking functions");

    if(extract_ranking_relation(converter))
      return false;

    return true;
  }
  else if(res==qdimacs_coret::P_UNSATISFIABLE)
  {
    return false;
  }
  else
    throw ("QBF SOLVER ERROR");
}

/*******************************************************************\

 Function: ranking_synthesis_qbft::extract_functions

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool ranking_synthesis_qbft::extract_ranking_relation(boolbvt &converter)
{
  replace_mapt replace_map;

  for(coefficient_mapt::const_iterator it=coefficient_map.begin();
      it!=coefficient_map.end();
      it++)
  {
    const exprt *sym=&it->second;
    while(sym->id()=="typecast")
      sym=&sym->op0();

    exprt value = converter.get(*sym); // this returns a constant.
    replace_map[*sym] = value;
    std::cout << from_expr(ns, "", it->second) << " = " << from_expr(ns, "", value) << std::endl;
  }

  if(const_coefficient.id()!="nil")
  {
    exprt value=converter.get(const_coefficient);
    std::cout << from_expr(ns, "", const_coefficient) << " = " << from_expr(ns, "", value) << std::endl;
    replace_map[const_coefficient]=value;
  }

  replace_expr(replace_map, rank_relation);
  simplify(rank_relation, ns);

  return false;
}

/*******************************************************************\

Function: ranking_synthesis_qbft::choose_qbf_core_extractor

  Inputs:

 Outputs:

 Purpose:

\********************************************************************/

qdimacs_coret *ranking_synthesis_qbft::choose_qbf_core_extractor(void) const
{
  #ifdef HAVE_QBF_CORE
//  return new qbf_bdd_coret();
//  return new qbf_skizzo_coret();
//  return new qbf_squolem_coret();
  return new qbf_qube_coret();
  #else
  throw "no QBF core support compiled in";
  #endif
}

/*******************************************************************\

 Function: ranking_synthesis_qbft::adjust_type

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void ranking_synthesis_qbft::adjust_type(typet &type) const
{
  if(type.id()=="bool")
  {
    type=uint_type();
    type.set("width", 1);
  }
}
