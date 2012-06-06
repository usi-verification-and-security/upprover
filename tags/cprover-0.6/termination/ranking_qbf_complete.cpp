/*******************************************************************\

Module: Ranking Function Synthesis (Complete QBF Synthesis)

Author: CM Wintersteiger

Date: October 2008

\*******************************************************************/

#include <base_type.h>

#include <solvers/sat/satcheck.h>

#include "ranking_qbf_complete.h"

/*******************************************************************\

 Function: ranking_synthesis_qbf_completet::value_variable

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

exprt ranking_synthesis_qbf_completet::value_variable(const exprt &expr)
{
  assert(expr.id()=="symbol");

  exprt &entry = value_variable_map[expr];

  if(entry==exprt())
  {
    // set up a new value variable (rx)
    entry.id("symbol");
    entry.set("identifier", expr.get("identifier").as_string() + "$R");

//    entry.type()=expr.type();

    // adjust the value type
    entry.type()=uint_type();
    entry.type().set("width", value_width);
  }

  return entry;
}

/*******************************************************************\

Function: ranking_synthesis_qbf_completet::extract_ranking_relation

  Inputs:

 Outputs:

 Purpose:

\********************************************************************/

exprt ranking_synthesis_qbf_completet::extract_ranking_relation(void)
{
  exprt termination_relation=and_exprt();

  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
  {
    exprt postsym=symbol_exprt(it->first, ns.lookup(it->first).type);
    exprt presym=symbol_exprt(it->second, ns.lookup(it->second).type);
        
    binary_relation_exprt bin(
      rank_function_map[presym],   // input ...
      ">",                    // ... greater than ...
      rank_function_map[postsym]); // ... output

    termination_relation.move_to_operands(bin);
  }

  if(termination_relation.operands().size()==0)
    termination_relation=false_exprt();
  else if(termination_relation.operands().size()==1)
  {
    exprt tmp=termination_relation.op0();
    termination_relation=tmp;
  }

  return termination_relation;
}

/*******************************************************************

 Function: ranking_synthesis_qbf_completet::extract_functions

 Inputs:

 Outputs:

 Purpose:

 \********************************************************************/

bool ranking_synthesis_qbf_completet::extract_functions(
  const exprt &templ,
  boolbvt &converter,
  qdimacs_coret &solver)
{
  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
  {
    for(unsigned toggle=0; toggle<2; toggle++)
    {
      exprt postsym=symbol_exprt(it->first, ns.lookup(it->first).type);
      exprt presym=symbol_exprt(it->second, ns.lookup(it->second).type);
          
      const exprt &val_var_sym = (toggle==0)?
                                   value_variable(presym): // get it from x
                                   value_variable(postsym); // get it from x'
      const typet &type=val_var_sym.type();

      exprt &rank_function=rank_function_map[(toggle==0)?presym:postsym];

      std::cout << "Extracting function for " << from_expr(ns, "", val_var_sym) <<
        std::endl;

      literalt l;

      unsigned width=bv_width(type);

      for(unsigned i=0; i<width; i++)
      {
        exprt this_func;

        if(converter.literal(val_var_sym, i, l))
        {
          // assume a don't care, so let's set it to false.
          this_func=false_exprt();
        }
        else
        {
          const exprt expr=solver.f_get(l);

          #if 0
          std::cout << "F[" << i << "] = " << from_expr(expr) << std::endl;
          #endif

          this_func=expr;
        }

        // cast the current function to unsigned
        typet rf_type=uint_type();
        rf_type.set("width", value_width);

        typecast_exprt cast(rf_type);
        cast.op()=this_func;

        if(i>0)
        {
          // shift it to the left
          exprt shift("shl", rf_type);
          shift.move_to_operands(cast);
          shift.copy_to_operands(from_integer(i, rf_type));

          // bitwise-or it with the old one.
          exprt bitwise("bitor", rf_type);
          bitwise.move_to_operands(shift);
          bitwise.move_to_operands(rank_function);

          rank_function=bitwise;
        }
        else
          rank_function=cast;
      }

      simplify(rank_function, ns);

      #if 0
      std::cout << "RF = " << from_expr(rank_function) << std::endl;
      #endif
    }

  }

  return false;
}

/********************************************************************\

 Function: ranking_synthesis_qbf_completet::instantiate

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

exprt ranking_synthesis_qbf_completet::instantiate(void)
{
  // build res == (R(x,x') -> rx>rx') && (x=x' -> rx=rx')

  exprt res("and", typet("bool"));
  binary_relation_exprt implication("=>");

  implication.lhs() = body.body_relation; // that's R(x,x')
  and_exprt rhs; // this is rx>rx'

  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
  {
    exprt postsym=symbol_exprt(it->first, ns.lookup(it->first).type);
    exprt presym=symbol_exprt(it->second, ns.lookup(it->second).type);
    
    exprt r_in=value_variable(presym);
    exprt r_out=value_variable(postsym);

    binary_relation_exprt bin(r_in, ">", r_out);
    rhs.operands().push_back(bin);
  }

  if(rhs.operands().size()==1)
    implication.rhs()=rhs.op0();
  else
    implication.rhs()=rhs;


  #if 0
  std::cout << "IMPLICATION: " << from_expr(implication) << std::endl;
  #endif

  res.move_to_operands(implication); // res = (R(x,x') -> rx>rx') now
//  res.move_to_operands(eq);

  and_exprt mono_constraint; // this is (x=x' -> rx=rx')

  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
  {
    exprt postsym=symbol_exprt(it->first, ns.lookup(it->first).type);
    exprt presym=symbol_exprt(it->second, ns.lookup(it->second).type);
        
    exprt eq_orig=equality_exprt(presym, postsym);
    exprt eq_values=equality_exprt(value_variable(presym),
                                   value_variable(postsym));

    binary_relation_exprt bin(eq_orig, "=>", eq_values);
    mono_constraint.move_to_operands(bin);
  }

  if(mono_constraint.operands().size()==1)
    res.move_to_operands(mono_constraint.op0());
  else
    res.move_to_operands(mono_constraint);

  return res;
}

/*******************************************************************\

 Function: ranking_synthesis_qbf_completet::generate_functions

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool ranking_synthesis_qbf_completet::generate_functions(void)
{
  #if 0
  std::cout << "GENERATE: " << templ << std::endl;
  #endif

  exprt templ = instantiate();
  qdimacs_coret::resultt res=qbf_solve_inc(templ);

  if(res==qdimacs_coret::P_SATISFIABLE)
  {
    status("Found ranking functions");

    rank_relation=extract_ranking_relation();

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

 Function: ranking_synthesis_qbf_completet::quantify_variables

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void ranking_synthesis_qbf_completet::quantify_variables(
  boolbvt &converter,
  qdimacs_coret &solver)
{
  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
  {
    exprt pre=symbol_exprt(it->second, ns.lookup(it->second).type);
    //base_type(pre, ns);
    
    #if 0
    std::cout << "Quantifying " << from_expr(pre) << " (" <<
      from_expr(post) << ")" << std::endl;
    #endif

    quantify_variable(converter, solver, pre, true); // x
    quantify_variable(converter, solver, value_variable(pre), false); // rx
  }

  for(intermediate_statet::const_iterator it=intermediate_state.begin();
      it!=intermediate_state.end();
      it++)
  {    
    exprt symbol=symbol_exprt(*it, ns.lookup(*it).type);
    //base_type(symbol, ns);
    
    quantify_variable(converter, solver, symbol, true);
  }

  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
  {
    exprt post=symbol_exprt(it->first, ns.lookup(it->first).type);
    //base_type(post, ns);
    
    // we assume that x' is determined by R(x,x')
    quantify_variable(converter, solver, post, true); // x'
    quantify_variable(converter, solver, value_variable(post), false); //rx'
  }
}

/*******************************************************************\

 Function: ranking_synthesis_qbf_completet::qbf_solve_inc

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

qdimacs_coret::resultt ranking_synthesis_qbf_completet::qbf_solve_inc(
  const exprt &templ)
{
  qdimacs_coret::resultt res=qdimacs_coret::P_SATISFIABLE;
  bool keep_going=true;
  refinement = true_exprt();

  while(keep_going && res==qdimacs_coret::P_SATISFIABLE)
  {
    status("Refining Skolem Functions");

    qdimacs_coret &solver=*choose_qbf_core_extractor();
    boolbvt converter(ns, solver);

//    solver->set_verbosity(get_verbosity());
//    solver->set_message_handler(get_message_handler());
//    converter.set_verbosity(get_verbosity());
//    converter.set_message_handler(get_message_handler());

    status("Template:");
    quantify_variables(converter, solver);

    std::cout << std::endl << from_expr(ns, "", templ) << std::endl;
    std::cout << "Refinement: " << from_expr(ns, "", refinement) << std::endl;

//    status("Converting template...");
    fine_timet before = current_time();
    converter.set_to_true(templ);
    converter.set_to_true(refinement);
    conversion_time+= current_time()-before;

//    if(get_verbosity()>5)
//        show_varmap(converter, std::cout);

//    status("Solving...");
    before = current_time();
    res = solver.prop_solve();
    solver_time += current_time()-before;

    if(res==qdimacs_coret::P_SATISFIABLE)
    {
      if(extract_functions(templ, converter, solver))
        return qdimacs_coret::P_ERROR;

      if(skolem_equality())
      {
        std::cout << "We found equal functions!" << std::endl;
        keep_going=false;
      }
      else
        std::cout << "Sadly the Skolem functions were not equal." << std::endl;
    }

    delete(&solver);
  }

  return res;
}

/*******************************************************************\

 Function: ranking_synthesis_qbf_completet::skolem_equality

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool ranking_synthesis_qbf_completet::skolem_equality(void)
{
  status("Checking equality");

  satcheckt sat_solver;
  boolbvt sat_converter(ns, sat_solver);

//  sat_solver.set_verbosity(get_verbosity());
//  sat_solver.set_message_handler(get_message_handler());
//  sat_converter.set_verbosity(get_verbosity());
//  sat_converter.set_message_handler(get_message_handler());

  // we need to check
  // \forall x,x' x==x' => f(x)==f(x')
  // the negation is
  // \exists x,x' x==x' && f(x)!=f(x')

  binary_relation_exprt implication("=>");
  implication.lhs() = and_exprt();
  implication.rhs() = or_exprt();

  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
  {
    exprt postsym=symbol_exprt(it->first, ns.lookup(it->first).type);
    exprt presym=symbol_exprt(it->second, ns.lookup(it->second).type);
    
    implication.lhs().copy_to_operands(equality_exprt(postsym, presym));

    binary_relation_exprt diseq("notequal");
    diseq.lhs()=rank_function_map[postsym];
    diseq.rhs()=rank_function_map[presym];

    implication.rhs().move_to_operands(diseq);
  }

  if(implication.lhs().operands().size()==0)
    return true;
  else if(implication.lhs().operands().size()==1)
  {
    exprt tmp=implication.lhs().op0();
    implication.lhs()=tmp;

    tmp=implication.rhs().op0();
    implication.rhs()=tmp;
  }

  fine_timet before=current_time();
  sat_converter.set_to_true(implication);
  conversion_time+=current_time()-before;

  before=current_time();
  satcheckt::resultt res=sat_solver.prop_solve();
  solver_time+=current_time()-before;

  if(res==satcheckt::P_UNSATISFIABLE)
    return true;
  else
  {
    // construct the refinement expr
    exprt next_step=and_exprt();

    for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
        it!=body.variable_map.end();
        it++)
    {
      exprt postsym=symbol_exprt(it->first, ns.lookup(it->first).type);
      exprt presym=symbol_exprt(it->second, ns.lookup(it->second).type);
          
      binary_relation_exprt diseq_pre("notequal");
      diseq_pre.lhs() = value_variable(presym);
      diseq_pre.rhs() = rank_function_map[presym];
      next_step.move_to_operands(diseq_pre);

      binary_relation_exprt diseq_post("notequal");
      diseq_post.lhs() = value_variable(postsym);
      diseq_post.rhs() = rank_function_map[postsym];
      next_step.move_to_operands(diseq_post);
    }

    and_exprt tmp(refinement, next_step);
    refinement=tmp;

    return false;
  }
}
