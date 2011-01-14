/*******************************************************************\

Module: Path Slicer

Author: Daniel Kroening
    
Date: September 2006

Purpose:

\*******************************************************************/

#include <assert.h>

#include <std_expr.h>
#include <std_types.h>
#include <hash_cont.h>
#include <prefix.h>

#include "path_slicer.h"

//#define DEBUG

class path_slicert
{
public:
  path_slicert(const namespacet &_ns):ns(_ns)
  {
  }

  void operator() (
    const abstract_functionst &abstract_functions,
    abstract_counterexamplet &abstract_counterexample);

protected:
  const namespacet &ns;
  
  typedef std::map<abstract_programt::const_targett,
                   abstract_functionst::function_mapt::const_iterator>
    function_mapt;
  function_mapt function_map;

  // dependency set
  typedef hash_set_cont<irep_idt, irep_id_hash> string_sett;

  friend std::ostream & operator<< (
    std::ostream &out,
    const string_sett &string_set)
  {
    for(string_sett::const_iterator it=string_set.begin();
        it!=string_set.end();
        it++)
      out << *it << std::endl;

    return out;
  }

  void get_suffixes(
    const std::string &base,
    const typet &type,
    string_sett &s);

  static void get_symbols(
    const exprt &expr,
    string_sett &s);

  void do_step(
    const abstract_functionst &abstract_functions,
    string_sett &dependencies,
    abstract_stept &step);
  
  void add_dependencies(const exprt &expr, string_sett &dest)
  {
    get_symbols(expr, dest);
  }
  
  bool depends_lhs(const exprt &expr, string_sett &dependencies);

  bool depends_lhs_rec(
    const exprt &expr,
    const string_sett &suffixes_r,
    const string_sett &suffixes_w,
    string_sett &dependencies,
    string_sett &new_dependencies);

  static bool depends(const string_sett &s, const string_sett &dependencies)
  {
    for(string_sett::const_iterator it=s.begin();
        it!=s.end();
        it++)
      if(dependencies.find(*it)!=dependencies.end())
        return true;

    return false;
  }
  
  static bool depends(const exprt &expr, const string_sett &dependencies)
  {
    string_sett tmp;
    get_symbols(expr, tmp);
    return depends(tmp, dependencies);
  }
  
  bool all_merge_to(
    const abstract_functionst &abstract_functions,
    const string_sett &dependencies,
    abstract_programt::const_targett src,
    abstract_programt::const_targett dest);
};

std::ostream & operator<< (
  std::ostream &out,
  const path_slicert::string_sett &string_set);

/*******************************************************************\

Function: path_slicert::all_merge_to

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool path_slicert::all_merge_to(
  const abstract_functionst &abstract_functions,
  const string_sett &dependencies,
  abstract_programt::const_targett src,
  abstract_programt::const_targett dest)
{
  // get the function we are in
  function_mapt::const_iterator f_it=function_map.find(src);
  assert(f_it!=function_map.end());

  const abstract_programt &abstract_program=f_it->second->second.body;

  std::set<abstract_programt::const_targett> seen;
  std::list<abstract_programt::const_targett> working_list;
  
  seen.insert(dest);
  working_list.push_back(src);
  
  while(!working_list.empty())
  {
    abstract_programt::const_targett t=working_list.back();
    working_list.pop_back();

    if(t==abstract_program.instructions.end())
      return false;

    // do we depend on s.th. that t changes?
    const goto_programt::instructiont &c_instruction=
      *t->code.concrete_pc;

    if(c_instruction.is_other() ||
       c_instruction.is_assign())
    {
      const irep_idt &statement=
        c_instruction.code.get_statement();

      // check if it's an assignment
      if(statement==ID_assign || statement=="init")
      {
        assert(c_instruction.code.operands().size()==2);

        const exprt &lhs=c_instruction.code.op0();
        
        string_sett tmp_dep(dependencies);
        if(depends_lhs(lhs, tmp_dep))
          return false;
      }
    }
  
    abstract_programt::const_targetst successors;
    
    abstract_program.get_successors(t, successors);
    
    if(successors.empty()) // termination!
      return false;

    for(abstract_programt::const_targetst::const_iterator
        it=successors.begin();
        it!=successors.end();
        it++)
    {
      abstract_programt::const_targett s=*it;
      
      if(seen.insert(s).second)
        working_list.push_back(s);
    }
  }
  
  return true;
}

/*******************************************************************\

Function: path_slicert::depends_lhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool path_slicert::depends_lhs(
  const exprt &expr,
  string_sett &dependencies)
{
  string_sett suffixes;
  get_suffixes("", expr.type(), suffixes);

  string_sett new_dependencies;

  bool result=
    depends_lhs_rec(
      expr,
      suffixes, // R
      suffixes, // W
      dependencies,
      new_dependencies);

  if(result) 
    dependencies.insert(
      new_dependencies.begin(),
      new_dependencies.end());

  return result;
}

/*******************************************************************\

Function: path_slicert::depends_lhs_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool path_slicert::depends_lhs_rec(
  const exprt &expr,
  const string_sett &suffixes_r,
  const string_sett &suffixes_w,
  string_sett &dependencies,
  string_sett &new_dependencies)
{
  if(expr.id()==ID_symbol)
  {
    string_sett tmp_r, tmp_w;

    const irep_idt &id=to_symbol_expr(expr).get_identifier();

    for(string_sett::const_iterator
        it=suffixes_w.begin();
        it!=suffixes_w.end();
        it++)
      tmp_w.insert(id2string(id)+id2string(*it));

    for(string_sett::const_iterator
        it=suffixes_r.begin();
        it!=suffixes_r.end();
        it++)
    {
      tmp_r.insert(id2string(id)+id2string(*it));
      #ifdef DEBUG
      std::cout << "tmp_r: " << id2string(id)+id2string(*it) << std::endl;
      #endif
    }
      
    // do we depend on it?
    if(!depends(tmp_r, dependencies))
    {
      #ifdef DEBUG
      std::cout << "NO DEPN\n";
      #endif
      return false; // no!
    }
    
    #ifdef DEBUG
    std::cout << "DEP!\n";
    #endif
    
    // yes! but we no longer do.
    for(string_sett::const_iterator it=tmp_w.begin();
        it!=tmp_w.end();
        it++)
      dependencies.erase(*it);
  }
  else if(expr.id()==ID_index)
  {
    assert(expr.operands().size()==2);
    get_symbols(expr.op0(), new_dependencies);
    get_symbols(expr.op1(), new_dependencies);

    string_sett tmp_r, tmp_w;

    for(string_sett::const_iterator it=suffixes_r.begin();
        it!=suffixes_r.end();
        it++)
    {
      tmp_r.insert(*it);
      tmp_r.insert("[]"+id2string(*it));
    }

    // can't get rid of array depenencies
    // thus, tmp_w stays empty

    return depends_lhs_rec(expr.op0(), tmp_r, tmp_w, dependencies, new_dependencies);
  }
  else if(expr.id()==ID_member)
  {
    assert(expr.operands().size()==1);

    string_sett tmp_r, tmp_w;

    for(string_sett::const_iterator it=suffixes_r.begin();
        it!=suffixes_r.end();
        it++)
    {
      tmp_r.insert(*it);
      tmp_r.insert("."+expr.get_string("component_name")+id2string(*it));
    }

    for(string_sett::const_iterator it=suffixes_w.begin();
        it!=suffixes_w.end();
        it++)
    {
      tmp_w.insert("."+expr.get_string("component_name")+id2string(*it));
    }

    return depends_lhs_rec(expr.op0(), tmp_r, tmp_w, dependencies, new_dependencies);
  }

  return true;
}

/*******************************************************************\

Function: path_slicert::get_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_slicert::get_symbols(const exprt &expr, string_sett &s)
{
  if(expr.id()==ID_symbol)
  {
    s.insert(to_symbol_expr(expr).get_identifier());
  }
  else if(expr.id()==ID_index)
  {
    assert(expr.operands().size()==2);
    string_sett tmp;
    get_symbols(expr.op0(), tmp);
    get_symbols(expr.op1(), s);

    for(string_sett::const_iterator
        it=tmp.begin();
        it!=tmp.end();
        it++)
      s.insert(id2string(*it)+"[]");
  }
  else if(expr.id()==ID_member)
  {
    assert(expr.operands().size()==1);

    string_sett tmp;

    get_symbols(expr.op0(), tmp);

    std::string suffix="."+expr.get_string(ID_component_name);

    for(string_sett::const_iterator
        it=tmp.begin();
        it!=tmp.end();
        it++)
      s.insert(id2string(*it)+suffix);
  }
  else
    forall_operands(it, expr)
      get_symbols(*it, s);
}

/*******************************************************************\

Function: path_slicert::get_suffixes

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_slicert::get_suffixes(
  const std::string &base,
  const typet &type,
  string_sett &s)
{
  const irep_idt &type_id=ns.follow(type).id();

  if(type_id==ID_struct || type_id==ID_union)
  {
    s.insert(base);

    const struct_typet &struct_type=to_struct_type(ns.follow(type));
    
    for(struct_typet::componentst::const_iterator
        c_it=struct_type.components().begin();
        c_it!=struct_type.components().end();
        c_it++)
    {
      const typet &subtype=c_it->type();
      const irep_idt &name=c_it->get(ID_name);
      get_suffixes(base+"."+id2string(name), subtype, s);
    }
  }
  else if(type_id==ID_array)
  {
    s.insert(base);
    get_suffixes(base+"[]", ns.follow(type).subtype(), s);
  }
  else
  {
    // no suffixes
    s.insert(base);
  }
}

/*******************************************************************\

Function: path_slicert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_slicert::operator()(
  const abstract_functionst &abstract_functions,
  abstract_counterexamplet &abstract_counterexample)
{
  #ifdef DEBUG
  std::cout << "Path slicer START" << std::endl;
  #endif 
  
  // build function map
  for(abstract_functionst::function_mapt::const_iterator
      f_it=abstract_functions.function_map.begin();
      f_it!=abstract_functions.function_map.end();
      f_it++)
  {
    for(abstract_programt::const_targett
        i_it=f_it->second.body.instructions.begin();
        i_it!=f_it->second.body.instructions.end();
        i_it++)
      function_map[i_it]=f_it;
  }

  string_sett dependencies;

  {  
    // last one must be assertion
    assert(!abstract_counterexample.steps.empty());
    assert(abstract_counterexample.steps.back().has_pc);
  
    // get concrete statement
    const goto_programt::instructiont &instruction=
      *abstract_counterexample.steps.back().pc->code.concrete_pc;

    assert(instruction.is_assert());
  
    // fill up dependencies
    add_dependencies(instruction.guard, dependencies);
  }
  
  #ifdef DEBUG
  std::cout << "***********\n";
  std::cout << dependencies;
  std::cout << "***********\n";
  #endif

  // go backwards

  for(abstract_counterexamplet::stepst::reverse_iterator
      it=abstract_counterexample.steps.rbegin();
      it!=abstract_counterexample.steps.rend();
      it++)
    do_step(abstract_functions, dependencies, *it);
}

/*******************************************************************\

Function: path_slicert::do_step

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_slicert::do_step(
  const abstract_functionst &abstract_functions,
  string_sett &dependencies,
  abstract_stept &step)
{
  if(!step.has_pc) return;

  // get abstract statement
  const abstract_programt::instructiont &a_instruction=
    *step.pc;
  
  // get concrete statement
  const goto_programt::instructiont &c_instruction=
    *a_instruction.code.concrete_pc;

  if(c_instruction.is_assign())
  {
    assert(c_instruction.code.operands().size()==2);

    const exprt &lhs=c_instruction.code.op0();
    const exprt &rhs=c_instruction.code.op1();
    
    if(depends_lhs(lhs, dependencies))
      add_dependencies(rhs, dependencies);
    else
      step.relevant=false;
  }
  else if(c_instruction.is_other())
  {
    const irep_idt &statement=
      c_instruction.code.get_statement();

    // check if it's an assignment
    if(statement=="init")
    {
      assert(c_instruction.code.operands().size()==2);

      const exprt &lhs=c_instruction.code.op0();
      const exprt &rhs=c_instruction.code.op1();
      
      if(depends_lhs(lhs, dependencies))
        add_dependencies(rhs, dependencies);
      else
        step.relevant=false;
    }
    else if(statement==ID_assign)
    {
      // shouldn't be here
      assert(false);
    }
    else if(statement==ID_expression)
    {
      // these don't do anything
      step.relevant=false;
    }
    else if(statement==ID_printf)
    {
      // doesn't do anything relevant
    }
    else
    {
      // arg!
      throw "path_slicert: unknown statement: `"+id2string(statement)+"'";
    }
  }
  else if(c_instruction.is_decl())
  {
    assert(c_instruction.code.operands().size()==1);

    if(!depends_lhs(c_instruction.code.op0(), dependencies))
      step.relevant=false;
  }
  else if(c_instruction.is_assume())
  {
    add_dependencies(c_instruction.guard, dependencies);
  }
  else if(c_instruction.is_goto())
  {
    if(c_instruction.guard.is_constant())
    {
      // ignore
    }
    else if(depends(c_instruction.guard, dependencies))
    {
      // it depends! add more dependencies
      add_dependencies(c_instruction.guard, dependencies);
    }
    else
    {
      // the abstract one must be the same goto
      assert(a_instruction.is_goto());
      
      // find out if we merge back to this on all paths
      assert(a_instruction.targets.size()==1);
      
      abstract_programt::const_targett dest;
      
      if(step.branch_taken)
        dest=a_instruction.targets.front();
      else
      {
        dest=step.pc;
        dest++;
      }
      
      if(all_merge_to(abstract_functions, dependencies, step.pc, dest))
      {
        step.relevant=false;
        #ifdef DEBUG
        std::cout << "GOTO is not relevant\n";
        #endif
      }
      else
      {
        #ifdef DEBUG
        std::cout << "GOTO is relevant\n";
        #endif
        add_dependencies(c_instruction.guard, dependencies);
      }
    }
  }
  else if(c_instruction.is_location() ||
          c_instruction.is_end_function())
    step.relevant=false;

  #ifdef DEBUG
  if(step.relevant)
    std::cout << "RELEVANT\n";
  else
    std::cout << "NOT RELEVANT\n";

  std::cout << "*******\n";
  std::cout << dependencies;
  std::cout << "*******\n";
  #endif
}

/*******************************************************************\

Function: path_slicer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void path_slicer(
  const namespacet &ns,
  const abstract_functionst &abstract_functions,
  abstract_counterexamplet &abstract_counterexample)
{
  path_slicert path_slicer(ns);

  path_slicer(
    abstract_functions,
    abstract_counterexample);
}
