/*******************************************************************\

Module: Variable Mapping HDL<->C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <set>

#include <expr_util.h>
#include <namespace.h>
#include <base_type.h>

#include "map_vars.h"

/*******************************************************************\

Function: is_program_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool is_program_symbol(const symbolt &symbol)
{
  return symbol.mode=="C" ||
         symbol.mode=="SpecC" ||
         symbol.mode=="cpp";
}

/*******************************************************************\

Function: instantiate_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instantiate_symbol(exprt &expr, unsigned cycle)
{
  if(expr.id()=="symbol" ||
     expr.id()=="nondet_symbol")
  {
    //const std::string &identifier=expr.get("identifier");

    expr.set("cycle", cycle);
  }
  else
    Forall_operands(it, expr)
      instantiate_symbol(*it, cycle);
}

/*******************************************************************\

   Class: map_varst

 Purpose:

\*******************************************************************/

#if 0
class map_varst:public messaget
{
 public:
  map_varst(contextt &_context, replace_mapt &_replace_map,
            message_handlert &_message):
    messaget(_message),
    context(_context), replace_map(_replace_map)
  { }

  void map_vars(const std::set<irep_idt> &modules);
  
 protected:
  contextt &context;
  replace_mapt &replace_map;

  symbolt &lookup(const irep_idt &identifier);

  void map_var(const std::set<irep_idt> &modules,
               const irep_idt &id,
               const exprt &expr,
               const symbolt::hierarchyt &hierarchy);

  void map_var(const exprt &symbol1, const symbolt &symbol2);

  std::string show_member(const exprt &expr);

  const symbolt &resolve_hierarchy
   (const std::set<irep_idt> &modules,
    const irep_idt &id,
    const exprt &expr,
    const symbolt::hierarchyt &hierarchy,
    bool module_instance);
};

/*******************************************************************\

Function: map_varst::lookup

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbolt &map_varst::lookup(const irep_idt &identifier)
{
  symbolst::iterator it=context.symbols.find(identifier);

  if(it==context.symbols.end())
    throw "failed to find identifier "+id2string(identifier);

  return it->second;
}

/*******************************************************************\

Function: map_varst::show_member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string map_varst::show_member(const exprt &expr)
{
  std::string result;

  if(expr.id()=="member")
  {
    if(expr.operands().size()!=1)
      throw "member expected to have one operand";

    result=show_member(expr.op0());
    result+=".";
    result+=expr.get_string("component_name");
  }
  else if(expr.id()=="index")
  {
    if(expr.operands().size()!=2)
      throw "index expected to have two operands";

    result=show_member(expr.op0());
    result+="[]";
  }
  else if(expr.id()=="symbol")
  {
    const symbolt &symbol=lookup(expr.get("identifier"));
    result=id2string(symbol.base_name);
  }

  return result;
}

/*******************************************************************\

Function: map_varst::map_var

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void map_varst::map_var(const exprt &symbol1, const symbolt &symbol2)
{
  // show to user

  print(6, "mapping "+show_member(symbol1)+" to "+
           id2string(symbol2.name)+"\n");

  // check types

  if(symbol1.type().id()!="unsignedbv" &&
     symbol1.type().id()!="signedbv" &&
     symbol1.type().id()!="bool")
  {
    throw "failed to map symbol "+show_member(symbol1)+
          " because of type "+symbol1.type().to_string();
  }

  if(symbol2.type.id()!="unsignedbv" &&
     symbol2.type.id()!="signedbv" &&
     symbol2.type.id()!="bool")
  {
    throw "failed to map symbol "+id2string(symbol2.name)+
          " because of type "+symbol2.type.to_string();
  }

  // map values

  exprt expr2(symbol_expr(symbol2));

  if(symbol1.type()!=symbol2.type)
    expr2.make_typecast(symbol1.type());

  replace_map.insert(std::pair<exprt, exprt>(symbol1, expr2));
}

/*******************************************************************\

Function: map_varst::resolve_hierarchy

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const symbolt &map_varst::resolve_hierarchy
 (const std::set<irep_idt> &modules,
  const irep_idt &id,
  const exprt &expr,
  const symbolt::hierarchyt &hierarchy,
  bool module_instance)
{
  symbolptr_listt symbolptr_list;

  forall_symbol_base_map(it, context.symbol_base_map, id)
  {
    const symbolt &s=lookup(it->second);

    if(s.is_type || s.free_var || 
       modules.find(s.module)==modules.end() ||
       s.hierarchy!=hierarchy)
      continue;

    if(module_instance!=(s.type.id()=="module_instance"))
      continue;
    
    symbolptr_list.push_back(&s);
  }

  if(symbolptr_list.empty())
  {
    print(1, "external identifier "+show_member(expr)+
             " not found\n");

    if(!hierarchy.empty())
    {
      print(1, "Hierarchy:\n");
      for(symbolt::hierarchyt::const_iterator it=
          hierarchy.begin();
          it!=hierarchy.end(); it++)
        print(1, "  "+id2string(*it)+"\n");
    }

    throw "failed to map variable";
  }
  else if(symbolptr_list.size()>=2)
  {
    print(1, "external identifier "+show_member(expr)+
             " does not uniquely resolve:\n");

    forall_symbolptr_list(it, symbolptr_list)
      print(1, "  "+id2string((*it)->name)+"\n");

    throw "failed to map variable";
  }

  // symbolptr_list has exactly one element

  return *symbolptr_list.front();
}

/*******************************************************************\

Function: map_varst::map_var

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void map_varst::map_var(const std::set<irep_idt> &modules,
                        const irep_idt &id,
                        const exprt &expr,
                        const symbolt::hierarchyt &hierarchy)
{
  if(expr.type().id()=="struct")
  {
    const irept::subt &components=
      expr.type().find("components").get_sub();

    forall_irep(it, components)
    {
      const irep_idt &name=it->get("name");

      const symbolt &symbol=
        resolve_hierarchy(modules, id, expr, hierarchy, true);

      symbolt::hierarchyt new_hierarchy(hierarchy);
      new_hierarchy.push_back(symbol.name);

      exprt new_expr("member", ((exprt &)(*it)).type());
      new_expr.copy_to_operands(expr);
      new_expr.set("component_name", name);

      map_var(modules, name, new_expr, new_hierarchy);
    }
  }
  else
  {
    const symbolt &symbol=
      resolve_hierarchy(modules, id, expr, hierarchy, false);

    map_var(expr, symbol);
  }
}

/*******************************************************************\

Function: map_varst::map_vars

  Inputs:

 Outputs:

 Purpose: Looks through context for external ANSI-C symbols
          Calls map_var to find mapping to HDL

\*******************************************************************/

void map_varst::map_vars(const std::set<irep_idt> &modules)
{
  Forall_symbols(it, context.symbols)
    if((it->second.mode=="C" || it->second.mode=="SpecC") &&
       it->second.is_extern)
    {
      symbolt::hierarchyt hierarchy;

      exprt expr=symbol_expr(it->second);

      namespacet ns(context);
      base_type(expr, ns);

      map_var(modules, it->second.base_name, expr, hierarchy);
    }
}

/*******************************************************************\

Function: map_vars

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void map_vars(contextt &context,
              const std::list<concrete_transition_systemt> &modules,
              replace_mapt &replace_map,
              message_handlert &message)
{
  // get names of top-level modules

  std::set<irep_idt> module_set;

  for(std::list<concrete_transition_systemt>::const_iterator it=
      modules.begin(); it!=modules.end(); it++)
    module_set.insert(it->symbol->name);

  map_varst map_vars(context, replace_map, message);

  map_vars.map_vars(module_set);
}

#endif
