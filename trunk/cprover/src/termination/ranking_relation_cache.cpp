/*******************************************************************\

Module: Ranking relation cache 

Author: CM Wintersteiger

\*******************************************************************/

#include <sstream>

#include <std_expr.h>
#include <prefix.h>

#include <langapi/language_util.h>

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>

#include "ranking_relation_cache.h"
#include "replace_identifier.h"

/********************************************************************\

 Function: ranking_relation_cachet::insert

 Inputs:

 Outputs:

 Purpose: 

\********************************************************************/

bool ranking_relation_cachet::insert(const exprt &rr)
{ 
  for(ranking_relationst::const_iterator it=ranking_relations.begin();
      it!=ranking_relations.end();
      it++)
    if(it->relation==rr) return false;
  
  ranking_relations.push_back(cache_entryt());
  ranking_relations.back().relation=rr;
  find_symbols(rr, ranking_relations.back().symbols);
  
  return true;
}

/********************************************************************\

 Function: ranking_relation_cachet::is_ranked

 Inputs:

 Outputs:

 Purpose: 

\********************************************************************/

bool ranking_relation_cachet::is_ranked(const exprt &body)
{
  find_symbols_sett path_symbols;
  find_symbols(body, path_symbols);
  
  for(ranking_relationst::const_iterator it=ranking_relations.begin();
      it!=ranking_relations.end();
      it++)
  {        
    const find_symbols_sett &rr_symbols=it->symbols;
    if(!is_subset(rr_symbols, path_symbols))
      continue;
    
    satcheckt solver;
    bv_pointerst converter(ns, solver);   
    
    solver.set_message_handler(get_message_handler());
    converter.set_message_handler(get_message_handler());
    solver.set_verbosity(2);
    converter.set_verbosity(2);
  
    and_exprt formula(body, not_exprt(it->relation));
    converter.set_to_true(formula);
  
    if(solver.prop_solve()==satcheckt::P_UNSATISFIABLE)
    {
      hit++;
      return true;
    }
  }
  
  miss++;
  return false;
}

/********************************************************************\

 Function: ranking_relation_cachet::disjunctive_relation

 Inputs:

 Outputs:

 Purpose: 

\********************************************************************/

exprt ranking_relation_cachet::disjunctive_relation(void) const
{
  if(ranking_relations.size()==0)
    return false_exprt();
  else if(ranking_relations.size()==1)
    return ranking_relations.front().relation;
  else
  {
    or_exprt res;
  
    for(ranking_relationst::const_iterator it=ranking_relations.begin();
        it!=ranking_relations.end();
        it++)
    {
      res.operands().push_back(it->relation);
    }
    
    return res;
  }
}
/********************************************************************\

 Function: ranking_relation_cachet::get_pre_post

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void ranking_relation_cachet::get_pre_post(
    const std::set<exprt> &symbols, 
    replace_idt &varmap) const
{
  varmap.clear();
  
  for(std::set<exprt>::const_iterator it=symbols.begin();
      it!=symbols.end();
      it++)
  {
    irep_idt id = it->get(ID_identifier);
    const std::string &id_s = id.as_string();    
    if (has_prefix(id_s, "termination"))
      varmap.insert(id, ID_nil);    
  }
  
  for(std::set<exprt>::const_iterator it=symbols.begin();
      it!=symbols.end();
      it++)
  {
    irep_idt id = it->get(ID_identifier);
    const std::string &id_s = id.as_string();    
    if (!has_prefix(id_s, "termination")) 
    {
      // This is an instrumented variable; we should have a 
      // corresponding pre-variable in varmap now.
      for (replace_idt::iterator vit=varmap.begin();
           vit!=varmap.end();
           vit++)
      {
        const irep_idt &pre = vit->first;
        if (pre.as_string().find(id_s)!=std::string::npos)
        {
          vit->second = id;
          break;
        }
      }
    }    
  }
  
  #ifdef _DEBUG
  for (replace_idt::iterator vit=varmap.begin();
       vit!=varmap.end();
       vit++)
  {
    assert(vit->second != ID_nil);
  }
  #endif
}

/********************************************************************\

 Function: ranking_relation_cachet::is_compositional

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool ranking_relation_cachet::is_compositional(void)
{
  //if(ranking_relations.size()==1)
  //  return true; // trivial!

  exprt disjunction = disjunctive_relation();
  
  if (!constraint.is_true())
    disjunction = and_exprt(disjunction, constraint);
  
  std::stringstream msg;
  msg << "Checking compositionality of: " << from_expr(ns, "", disjunction);
  debug(msg.str());  
    
  std::set<exprt> symbols;  
  find_symbols(disjunction, symbols);
  
  // Get a proper pre/post-mapping
  replace_idt varmap;
  get_pre_post(symbols, varmap);
  
  
  satcheckt checker;
  bv_pointerst converter(ns, checker);
  
  std::set<exprt> new_symbols;

  exprt d_post1 = disjunction; replace_idt p1_replacer;
  exprt d_post2 = disjunction; replace_idt p2_replacer;
  
  for(replace_idt::const_iterator it=varmap.begin();
      it!=varmap.end();
      it++)
  {
    const irep_idt &pre = it->first;
    const irep_idt &post = it->second;
        
    p1_replacer.insert(post, "LINK::"+post.as_string());
    p2_replacer.insert(pre,  "LINK::"+post.as_string());
  }
  
  p1_replacer.replace(d_post1);
  p2_replacer.replace(d_post2);

  #if 0
  std::cout << "1st: " << d_post1 << std::endl;
  std::cout << "2nd: " << d_post2 << std::endl;
  #endif

  exprt post = and_exprt(d_post1, d_post2);
  implies_exprt f( post, disjunction );  

  #if 0
  std::cout << "Check: " << from_expr(ns, "", f) << std::endl;
  #endif
    
  converter.set_to_true(not_exprt( f ));
  
  bv_pointerst::resultt res = converter.dec_solve();
  
  if (res != decision_proceduret::D_SATISFIABLE &&
      res != decision_proceduret::D_UNSATISFIABLE)
    throw "SAT SOLVER PROBLEM";
  
  return res==decision_proceduret::D_UNSATISFIABLE;  
}
