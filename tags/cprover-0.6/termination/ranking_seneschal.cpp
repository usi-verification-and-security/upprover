/*******************************************************************\

Module: Ranking Function Synthesis (Seneschal backend)

Author: CM Wintersteiger

Date: May 2009

\*******************************************************************/

#include <memory>
#include <fstream>
#include <sstream>

#include <std_expr.h>
#include <simplify_expr.h>
#include <i2string.h>
#include <str_getline.h>
#include <find_symbols.h>
#include <prefix.h>

#include <langapi/language_util.h>

#include "expr2seneschal.h"
#include "rankfunction_typecheck.h"
#include "ranking_seneschal.h"


/********************************************************************\

 Function: ranking_synthesis_seneschalt::instantiate_template

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

exprt ranking_synthesis_seneschalt::instantiate(void)
{
  exprt path = body.body_relation;

  if(!write_input_file(path))
    return nil_exprt();

  // make sure nothing is saved
  rank_relation = false_exprt();

  return true_exprt();
}

/*******************************************************************\

 Function: ranking_synthesis_seneschalt::generate_functions

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool ranking_synthesis_seneschalt::generate_functions(void)
{
  #if 0
  std::cout << "GENERATE: " << templ << std::endl;
  #endif


  if(instantiate()==nil_exprt())
    return false;

  std::cout << "INPUT IS: " << std::endl;
  system("cat seneschal.input");

  status("Calling seneschal...");
  fine_timet before = current_time();
  system(">seneschal.out ; >seneschal.err; "
         "seneschal seneschal.input 1> seneschal.out 2> seneschal.err");
  solver_time += current_time()-before;
  solver_calls++;


	{
		std::cout << "STDOUT WAS: " << std::endl;
		system("cat seneschal.out");
		std::cout << "STDERR WAS: " << std::endl;
		system("cat seneschal.err");
	}

	exprt rf("nil");
	if(!read_output(rf)) throw ("SENESCHAL ERROR");

//  remove("seneschal.input");
//  remove("seneschal.err");
//  remove("seneschal.out");

  if(rf.id()!="nil")
  {
    if(!extract_ranking_relation(rf))
      return false;

    return true;
  }
  else
    return false;
}

/*******************************************************************

 Function: ranking_synthesis_seneschalt::extract_functions

 Inputs:

 Outputs:

 Purpose:

 \********************************************************************/

bool ranking_synthesis_seneschalt::extract_ranking_relation(exprt &rf)
{
  exprt function = rf;
  replace_mapt post_replace_map;

  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
  {
    if(used_variables.find(it->first)==used_variables.end())
      continue;
    
    exprt postsym=symbol_exprt(it->first, ns.lookup(it->first).type);
    exprt presym=symbol_exprt(it->second, ns.lookup(it->second).type);
    
    post_replace_map[presym] = postsym;
  }

  for(intermediate_statet::const_iterator it=intermediate_state.begin();
      it!=intermediate_state.end();
      it++)
  {
    const exprt e=symbol_exprt(*it);

    // Get rid of SSA-numbers
    const std::string &str = it->as_string();
    exprt ne=e;
    ne.set("identifier", str.substr(0, str.find('#')));
    ne.type()=ns.lookup(ne.get("identifier")).type;
  }

  simplify(function, ns);

  exprt post_function = function;
  replace_expr(post_replace_map, post_function);

  rank_relation = binary_relation_exprt(post_function, "<", function);

  return true;
}

/*******************************************************************

 Function: ranking_synthesis_seneschalt::write_input_file

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool ranking_synthesis_seneschalt::write_input_file(const exprt &e)
{
  assert(e.id()=="and" && e.type()==bool_typet());

  std::ofstream f("seneschal.input");

  exprt e_ext = e;
  replace_mapt rmap;
  std::set<irep_idt> inputs, outputs;

  collect_variables(e_ext, rmap, inputs, outputs);

  // write variable declarations
  write_variables(f, inputs, outputs);
  f << std::endl;

  // translate constraints
  if(!write_constraints(f, rmap, e_ext))
    return false;

  f << std::endl;

  f.close();

  return true;
}

/*******************************************************************

 Function: ranking_synthesis_seneschalt::read_output

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool ranking_synthesis_seneschalt::read_output(exprt &rf)
{
  // Check if there is a result at all...
  std::ifstream err("seneschal.err");
  bool result_found=false;
  while(err)
  {
    std::string line;
    str_getline(err, line);
    if(line=="Solving ... no solution" ||
       line=="Solving ... found a solution")
    {
      result_found = true;
      break;
    }
  }
  err.close();

  if(!result_found) return false;

  // There is a result!
  std::ifstream in("seneschal.out");

  std::string rank_string;
  std::string bound_string;

  while(in)
  {
    std::string line;

    str_getline(in, line);

    if(line.substr(0,7)=="Ranking")
    {
      std::vector<std::string> tokens;
      tokenize(line, tokens, " =[],\tr");

      bool work=false;
      for(std::vector<std::string>::const_iterator it=tokens.begin();
          it!=tokens.end();
          it++)
      {
        // std::cout << "TOKEN: " << *it << std::endl;

        if(*it=="Ranking")
        {
          result_found=true;
          work=true;
        }
        else if(*it=="function:") /* SKIP */ ;
        else if(work)
        {
          rank_string += " " + *it;
        }
      }
    }
    else if(line.substr(0,25)=="Lower bound (post-state):")
    {
      std::vector<std::string> tokens;
      tokenize(line, tokens, " =[],\t");

      std::vector<std::string>::const_iterator it=tokens.begin();
      it++; it++; it++;
      if(it!=tokens.end())
      {
        //std::cout << "TOKEN: " << *it << std::endl;

        bound_string = *it;
      }
    };
  }

  if(rank_string!="")
  {
    bound = string2integer(bound_string);

    if(bound!=0)
      rank_string = "(" + rank_string + ") - (" + bound_string + ")";

    exprt rfl;

    if(parse_rank_function(rank_string, trans_context, ns, *message_handler, rfl))
      throw ("RF EXTRACTION ERROR");

    replace_expr(variable_map, rfl);
    std::cout << "FOUND FUNCTION: " << from_expr(ns, "", rfl) << std::endl;

    rf.swap(rfl);

    std::cout << "BOUND: " << bound << std::endl;
  }
    
  return true;
}

/*******************************************************************

 Function: ranking_synthesis_seneschalt::write_variables

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void ranking_synthesis_seneschalt::write_variables(
  std::ostream &f,
  const std::set<irep_idt> &inputs,
  const std::set<irep_idt> &outputs) const
{
  f << " \\from{ ";
  for (std::set<irep_idt>::const_iterator it=inputs.begin();
       it!=inputs.end();
       it++)
  {
    f << *it << "; ";
  }
  f << "} " << std::endl;

  f << " \\to{ ";
  for (std::set<irep_idt>::const_iterator it=outputs.begin();
       it!=outputs.end();
       it++)
  {
    f << *it << "; ";
  }
  f << "}" << std::endl;
}

/*******************************************************************

 Function: ranking_synthesis_seneschalt::write_constraints

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool ranking_synthesis_seneschalt::write_constraints(
  std::ostream &f,
  replace_mapt &rmap,
  exprt e)
{
  expr2seneschalt expr2seneschal(ns);
  f << " \\transition {" << std::endl;

  bool first=true;
  forall_operands(it, e)
  {
    exprt t = *it;
    replace_expr(rmap, t);

    {
      if(!first) f << " & " << std::endl;

      try {
        f << "  " << expr2seneschal.convert(t, false, true);
      }
      catch (const expr2seneschalt::UnhandledException &ex)
      {
        status("Seneschal unsuitable: " + ex.reason.id_string());
        status("In: " + from_expr(ns, "", t));
        return false;
      }

      first=false;
    }
  }

  f << std::endl << " }";

  return true;
}

/*******************************************************************

 Function: ranking_synthesis_seneschalt::collect_variables

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void ranking_synthesis_seneschalt::collect_variables(
  exprt &e_ext,
  replace_mapt &rmap,
  std::set<irep_idt> &inputs,
  std::set<irep_idt> &outputs)
{
  unsigned v=1;

  // collect inputs/outputs
  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
  {
    if(used_variables.find(it->first)==used_variables.end())
      continue;
    
    exprt postsym=symbol_exprt(it->first, ns.lookup(it->first).type);
    exprt presym=symbol_exprt(it->second, ns.lookup(it->second).type);
        
    irep_idt ident = it->second;
    irep_idt newi = std::string("I") + i2string(v);
    rmap[presym] = symbol_exprt(newi, presym.type());
    inputs.insert(newi);

    exprt reverse = rmap[presym];
    reverse.set("identifier", std::string("c::") + newi.as_string());
    variable_map[reverse] = presym;

    symbolt s;
    s.name = std::string("c::") + newi.as_string();
    s.base_name = newi;
    s.type = presym.type();
    trans_context.move(s);

    ident = it->first;
    newi = std::string("O") + i2string(v++);
    rmap[postsym] = symbol_exprt(newi, postsym.type());
    outputs.insert(newi);

    exprt r("seneschal-range");

    std::string str = std::string("in") +
      ((presym.type().id()=="unsignedbv" ||
        presym.type().id()=="bool")?"U":"") +
      i2string(safe_width(presym, ns));

    r.copy_to_operands(presym);
    r.type() = typet(str);

    e_ext.move_to_operands(r);
  }

  // collect intermediates
  unsigned nondet_cnt = 0;
  for(intermediate_statet::const_iterator it=intermediate_state.begin();
      it!=intermediate_state.end();
      it++)
  {
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
    
    
    // define an input variable for them.    
    irep_idt newi = (is_nondet) ?
                       std::string("N") + i2string(nondet_cnt) :
                       std::string("I") + i2string(v); // no v++!
    rmap[sym] = exprt("symbol");
    rmap[sym].set("identifier", newi);
    inputs.insert(newi);

    exprt reverse = rmap[sym];
    reverse.set("identifier", std::string("c::") + newi.as_string());
    variable_map[reverse] = sym;

    symbolt s;
    s.name = std::string("c::") + newi.as_string();
    s.base_name = newi;
    s.type = sym.type();
    trans_context.move(s);

    // AND define an output variable.
    irep_idt newo = (is_nondet) ?
                                 std::string("N") + i2string(nondet_cnt++) + "'" :
                                 std::string("O") + i2string(v++);
    outputs.insert(newo);
    
    // define the range of the new variable
    exprt r("seneschal-range");

    std::string str = std::string("in") +
      ((sym.type().id()=="unsignedbv" ||
       sym.type().id()=="bool")?"U":"") +
      i2string(safe_width(sym, ns));

    r.copy_to_operands(sym);
    r.type() = typet(str);

    e_ext.move_to_operands(r);

    if(is_nondet)
    {
      // add a constraint
      exprt os = symbol_exprt(newo, sym.type());
      equality_exprt eq(os,rmap[sym]);
      e_ext.move_to_operands(eq);
    }
  }
}

