/*******************************************************************\

Module: Ranking Function Synthesis (QBF Bitwise Coefficient Synthesis)

Author: CM Wintersteiger

Date: May 2009

\*******************************************************************/

#include <memory>

#include <math.h>
#include <std_expr.h>
#include <arith_tools.h>
#include <simplify_expr.h>
#include <i2string.h>

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

#include "ranking_qbf_bitwise.h"

#define CONSTANT_COEFFICIENT_ID "termination::constant"

/*******************************************************************\

Function: ranking_synthesis_qbf_bitwiset::quantify_variables

  Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void ranking_synthesis_qbf_bitwiset::quantify_variables(
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

    exprt nsym(*sym);
    std::string original_id=sym->get("identifier").as_string();
    //base_type(nsym, ns);

    for(unsigned i=0; i<bitwise_width; i++)
    {
      if(i!=0) nsym.set("identifier", original_id + "@" + i2string(i));
      quantify_variable(converter, solver, nsym, false);
    }
  }

  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
  {    
    if(used_variables.find(it->first)==used_variables.end())
      continue;
    
    exprt presym=symbol_exprt(it->second, ns.lookup(it->second).type);    
    //base_type(presym, ns);
    
    #if 0
    std::cout << "Quantifying " << from_expr(pre) << " (" <<
      from_expr(post) << ")" << std::endl;
    #endif

    quantify_variable(converter, solver, presym, true); // x
  }

  for(intermediate_statet::const_iterator it=intermediate_state.begin();
      it!=intermediate_state.end();
      it++)
  {
    if(used_variables.find(*it)==used_variables.end())
        continue;
    
    irep_idt ident=(it->as_string().substr(0, it->as_string().rfind('@')));
    ident=(ident.as_string().substr(0, ident.as_string().rfind('#')));
    exprt symbol=symbol_exprt(ident, ns.lookup(ident).type);
    //base_type(symbol, ns);
    
    quantify_variable(converter, solver, symbol, true);
  }

  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
  {
    if(used_variables.find(it->first)==used_variables.end())
      continue;
    
    exprt postsym=symbol_exprt(it->first, ns.lookup(it->first).type);
    //base_type(postsym, ns);
    
    // we assume that x' is determined by R(x,x')
    quantify_variable(converter, solver, postsym, true); // x'
  }

}

/********************************************************************\

 Function: ranking_synthesis_qbf_bitwiset::instantiate_template

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

exprt ranking_synthesis_qbf_bitwiset::instantiate(void)
{
  find_largest_constant(body.body_relation);

  binary_relation_exprt implication("=>");
  implication.lhs() = body.body_relation; // that's R(x,x')

  implication.rhs() =
    (function_class==F_AFFINE)      ? instantiate_affine() :
    (function_class==F_DISJUNCTIVE) ? instantiate_disjunctive() :
    (function_class==F_CONJUNCTIVE) ? instantiate_conjunctive() :
    (function_class==F_PROJECTIONS) ? instantiate_projections() :      
                                      instantiate_nothing();

  // save the relation for later
  rank_relation = implication.rhs();

  return implication;
}

/********************************************************************\

 Function: ranking_synthesis_qbf_bitwiset::instantiate_nothing

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

exprt ranking_synthesis_qbf_bitwiset::instantiate_nothing(void)
{
  return false_exprt(); // Nothing: there is no ranking function at all
}

/********************************************************************\

 Function: ranking_synthesis_qbf_bitwiset::instantiate_projections

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

exprt ranking_synthesis_qbf_bitwiset::instantiate_projections(void)
{
  std::pair<exprt,exprt> dlt = duplicate(ite_template(), bitwise_width);

  if(bitwise_width<=1)
  {
    dlt.second.negate();
    return binary_relation_exprt(dlt.second, "and", dlt.first);
  }
  else
    return binary_relation_exprt(dlt.second, "<", dlt.first);
}

/********************************************************************\

 Function: ranking_synthesis_qbf_bitwiset::instantiate_affine

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

exprt ranking_synthesis_qbf_bitwiset::instantiate_affine(void)
{
  std::pair<exprt,exprt> dlt = duplicate(affine_template("notequal", "and"),
                                         bitwise_width);

  if(bitwise_width<=1)
  {
    dlt.second.negate();
    return binary_relation_exprt(dlt.second, "and", dlt.first);
  }
  else
    return binary_relation_exprt(dlt.second, "<", dlt.first);
}

/********************************************************************\

 Function: ranking_synthesis_qbf_bitwiset::instantiate_disjuntive

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

exprt ranking_synthesis_qbf_bitwiset::instantiate_disjunctive(void)
{
  std::pair<exprt,exprt> dlt = duplicate(affine_template("or", "and"),
                                         bitwise_width);

  if(bitwise_width<=1)
  {
    dlt.second.negate();
    return binary_relation_exprt(dlt.second, "and", dlt.first);
  }
  else
    return binary_relation_exprt(dlt.second, "<", dlt.first);
}

/********************************************************************\

 Function: ranking_synthesis_qbf_bitwiset::instantiate_conjunctive

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

exprt ranking_synthesis_qbf_bitwiset::instantiate_conjunctive(void)
{
  std::pair<exprt,exprt> dlt = duplicate(affine_template("and", "or"),
                                         bitwise_width);

  if(bitwise_width<=1)
  {
    dlt.second.negate();
    return binary_relation_exprt(dlt.second, "and", dlt.first);
  }
  else
    return binary_relation_exprt(dlt.second, "<", dlt.first);
}

/*******************************************************************\

 Function: ranking_synthesis_qbf_bitwiset::coefficient

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

exprt ranking_synthesis_qbf_bitwiset::coefficient(const exprt &expr)
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
    entry.type()=expr.type();

    assert(expr.type().id()=="signedbv" ||
           expr.type().id()=="unsignedbv" ||
           expr.type().id()=="bool");
  }

  return entry;
}

/*******************************************************************\

 Function: ranking_synthesis_qbf_bitwiset::generate_functions

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool ranking_synthesis_qbf_bitwiset::generate_functions(void)
{
  #if 0
  std::cout << "GENERATE: " << templ << std::endl;
  #endif

  qdimacs_coret::resultt res=qdimacs_coret::P_UNSATISFIABLE;
  
  unsigned state_size = get_state_size();
  
  status("Termination: state size is " + i2string(state_size));

  while (res==qdimacs_coret::P_UNSATISFIABLE && 
         bitwise_width <= state_size)
  {
    std::auto_ptr<qdimacs_coret> solver(choose_qbf_core_extractor());
    bv_pointerst converter(ns, *solver);

    solver->set_verbosity(get_verbosity());
    solver->set_message_handler(get_message_handler());
    converter.set_verbosity(get_verbosity());
    converter.set_message_handler(get_message_handler());

    exprt templ = instantiate();

    status("Template:");
    quantify_variables(converter, *solver);

    std::cout << std::endl << from_expr(ns, "", templ) << std::endl;

    status("Converting template...");
    fine_timet before = current_time();
    converter.set_to_true(templ);
    fine_timet ctime = current_time()-before;

    if(get_verbosity()>5)
        show_varmap(converter, std::cout);

    status("Solving...");
    before = current_time();
    res = solver->prop_solve();
     
    // solver_calls++; // we don't count calls or time globally.
    status(std::string("TConversion time: ") +
           time2string(ctime) + " sec.");
    status(std::string("TSolver time: ") +
           time2string(current_time()-before) + " sec.");
    status(std::string("TSolver calls: 1"));

    if(res==qdimacs_coret::P_SATISFIABLE)
    {
      status("Found ranking functions");

      if(extract_ranking_relation(converter))
        return false;
    }
    else
    {
      bitwise_width++;
      if(bitwise_width <= state_size)
        status("No ranking functions found; increasing width to " +
               i2string(bitwise_width));
    }
  }

  if(res==qdimacs_coret::P_SATISFIABLE)
    return true;
  else if(res==qdimacs_coret::P_UNSATISFIABLE)
    return false;
  else
    throw ("QBF SOLVER ERROR");
}

/*******************************************************************\

 Function: ranking_synthesis_qbf_bitwiset::extract_functions

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool ranking_synthesis_qbf_bitwiset::extract_ranking_relation(boolbvt &converter)
{
  replace_mapt replace_map;

  for(coefficient_mapt::const_iterator it=coefficient_map.begin();
      it!=coefficient_map.end();
      it++)
  {
    const exprt *sym=&it->second;
    while(sym->id()=="typecast")
      sym=&sym->op0();

    if(bitwise_width<=1)
    {
      exprt value;      
      value=converter.get(*sym); // this returns a constant.      
      
      replace_map[*sym] = value;
      std::cout << from_expr(ns, "", it->second) << " = " << from_expr(ns, "", value) << std::endl;
    }
    else
    {
      assert(sym->id()=="symbol");
      exprt nsym(*sym);
      std::string original_id=sym->get("identifier").as_string();

      for(unsigned i=0; i<bitwise_width; i++)
      {
        if(i!=0) nsym.set("identifier", original_id + "@" + i2string(i));
        exprt value = converter.get(nsym);
        replace_map[nsym] = value; // bit i
        std::cout << from_expr(ns, "", nsym) << " = " << from_expr(ns, "", value) << std::endl;
      }
    }
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

 Function: ranking_synthesis_qbf_bitwiset::xor_bits

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

exprt ranking_synthesis_qbf_bitwiset::bitwise_chain(
  const irep_idt &termOp,
  const exprt &expr) const
{
  unsigned width=safe_width(expr, ns);

  assert(width>0);

  if(width==1)
  {
    if(expr.type()!=bool_typet())
    {
      typecast_exprt t(typet("bool"));
      t.op() = expr;
      return t;
    }
    else
      return expr;
  }

  exprt res;

  exprt e("extractbit", bool_typet());
  e.copy_to_operands(expr);

  res = e;
  res.copy_to_operands(from_integer(0, typet("natural")));

  for(unsigned i=1; i<width; i++)
  {
    if(termOp=="notequal")
    {
      exprt t("=", bool_typet());
      t.copy_to_operands(res, e);
      t.op1().copy_to_operands(from_integer(i, typet("natural")));
      res=not_exprt(t);
    }
    else
    {
      exprt t(termOp, bool_typet());
      t.copy_to_operands(res, e);
      t.op1().copy_to_operands(from_integer(i, typet("natural")));
      res=t;
    }
  }

  return res;
}

/*******************************************************************\

 Function: ranking_synthesis_qbf_bitwiset::affine_template

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

std::pair<exprt,exprt> ranking_synthesis_qbf_bitwiset::affine_template(
  const irep_idt &termOp,
  const irep_idt &coefOp)
{
  exprt function;
  replace_mapt pre_replace_map;

  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
  {
    if(used_variables.find(it->first)==used_variables.end())
      continue;
    
    exprt postsym=symbol_exprt(it->first, ns.lookup(it->first).type);
    exprt presym=symbol_exprt(it->second, ns.lookup(it->second).type);
        
    pre_replace_map[postsym] = presym; // save the corresponding pre-var
    exprt var=postsym;
    adjust_type(var.type());

    exprt co = coefficient(var);
    irep_idt bitop = (coefOp=="and")      ? "bitand" :
                     (coefOp=="or")       ? "bitor"  :
                     (coefOp=="notequal") ? "bitxor" : 
                                            "";

    exprt varblock(bitop, var.type());
    varblock.copy_to_operands(var, co);

    exprt bchain = bitwise_chain(termOp, varblock);

    if(it==body.variable_map.begin()) // first one
      function=bchain;
    else
    {
      if(termOp=="notequal")
      {
        exprt t("=", bool_typet());
        t.move_to_operands(function);
        t.move_to_operands(bchain);
        function=not_exprt(t);
      }
      else
      {
        exprt t(termOp, bool_typet());
        t.move_to_operands(function);
        t.move_to_operands(bchain);
        function=t;
      }
    }
  }

  // ... and a constant coefficient
  symbol_exprt const_sym(CONSTANT_COEFFICIENT_ID, bool_typet());
  const_coefficient=coefficient(const_sym);

  
  if(termOp=="notequal")
  {
    exprt t("=", bool_typet());
    t.move_to_operands(function);
    t.copy_to_operands(const_coefficient);
    function = not_exprt(t);
  }
  else
  {
    exprt t(termOp, bool_typet());
    t.move_to_operands(function);
    t.copy_to_operands(const_coefficient);
    function = t;
  }

  exprt pre_function=function;
  replace_expr(pre_replace_map, pre_function);

  return std::pair<exprt,exprt>(pre_function, function);
}

/*******************************************************************\

 Function: ranking_synthesis_qbf_bitwiset::ite_template

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

std::pair<exprt,exprt> ranking_synthesis_qbf_bitwiset::ite_template()
{
  exprt function;
  replace_mapt pre_replace_map;
    
  unsigned state_size = get_state_size();
  unsigned bits = log(state_size)/log(2) + 1;  
  
  symbol_exprt const_sym(CONSTANT_COEFFICIENT_ID, unsignedbv_typet(bits));
  const_coefficient=coefficient(const_sym);
    
  unsigned cnt=0;
  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
  {
    if(used_variables.find(it->first)==used_variables.end())
      continue;
    
    exprt postsym=symbol_exprt(it->first, ns.lookup(it->first).type);
    exprt presym=symbol_exprt(it->second, ns.lookup(it->second).type);
        
    pre_replace_map[postsym] = presym; // save the corresponding pre-var
    exprt var=postsym;
    adjust_type(var.type());

    unsigned vwidth = safe_width(var, ns);
    for(unsigned i=0; i<vwidth; i++)
    {
      exprt t("extractbit", bool_typet());
      t.copy_to_operands(var);
      t.copy_to_operands(from_integer(i, typet("natural")));
      
      if(it==body.variable_map.begin() && i==0)
        function = t;
      else
      {
        function =           
          if_exprt(equality_exprt(const_coefficient, 
                                  from_integer(cnt, const_coefficient.type())),
                   t,
                   function);        
      }      
      
      cnt++;
    }
  }
  
  exprt pre_function=function;
  replace_expr(pre_replace_map, pre_function);
  
  return std::pair<exprt,exprt>(pre_function, function);
}
  
/*******************************************************************\

 Function: ranking_synthesis_qbf_bitwiset::duplicate

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

std::pair<exprt,exprt> ranking_synthesis_qbf_bitwiset::duplicate(
   const std::pair<exprt,exprt> pp,
   unsigned bits)
{
  if(bits<=1) return pp;

  std::pair<exprt,exprt> res;
  res.first.id("concatenation"); res.first.type() = unsignedbv_typet(bits);
  res.second.id("concatenation"); res.second.type() = unsignedbv_typet(bits);

  std::vector<replace_mapt> replace_maps(bits);

  for(coefficient_mapt::const_iterator it=coefficient_map.begin();
      it!=coefficient_map.end();
      it++)
  {
    const exprt *sym=&it->second;
    while(sym->id()=="typecast")
      sym=&sym->op0();

    assert(sym->id()=="symbol");
    exprt nsym(*sym);
    std::string original_id=sym->get("identifier").as_string();

    for(unsigned i=1; i<bits; i++)
    {
      nsym.set("identifier", original_id + "@" + i2string(i));
      replace_maps[i][*sym] = nsym;
    }
  }

  for(int i=bits-1; i>0; i--)
  {
    exprt pre=pp.first;
    exprt post=pp.second;

    replace_expr(replace_maps[i], pre);
    replace_expr(replace_maps[i], post);

    res.first.move_to_operands(pre);
    res.second.move_to_operands(post);
  }

  res.first.copy_to_operands(pp.first); // 0-bit is not renamed!
  res.second.copy_to_operands(pp.second);

  return res;
}

/*******************************************************************\

 Function: ranking_synthesis_qbf_bitwiset::get_state_size

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

unsigned ranking_synthesis_qbf_bitwiset::get_state_size(void) const
{
  unsigned res=0;  
      
  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
    res += safe_width(symbol_exprt(it->first, ns.lookup(it->first).type), ns);    
  
  assert(res>0);
  
  return res;
}
