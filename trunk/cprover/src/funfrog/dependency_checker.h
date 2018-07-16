#ifndef CPROVER_DEPENDECY_CHECKER_H
#define CPROVER_DEPENDECY_CHECKER_H

#include <util/symbol.h>
#include <util/ui_message.h>
#include <util/time_stopping.h>

#include <goto-symex/symex_target_equation.h>
#include <goto-symex/slice.h>

#include <funfrog/utils/UnionFind.h>
#include <map>


class smt_symex_target_equationt;
class goto_programt;
class namespacet;
class subst_scenariot;
class partitioning_target_equationt;

#define INDEPT false
#define DEPT true

#define NOTIMP false
#define IMP true


class dependency_checkert : public messaget
{
public:
    dependency_checkert(
          const namespacet &_ns,
          ui_message_handlert &_message_handler,
          const goto_programt &_goto_program,
          subst_scenariot &_omega,
          //int percentage
          int fraction,
          unsigned int SSA_steps_size
    ) :
          goto_program(_goto_program),
          ns(_ns),
          message_handler (_message_handler),
          omega(_omega)
    {
          set_message_handler(_message_handler);
          //last_label could be useless after the updates
          //last_label = 0;
          impl_timeout = 2000;
          // FIXME: make treshold parametrized
          treshold = fraction; //equation.SSA_steps.size() / fraction;
          //treshold = percentage * equation.SSA_steps.size() / 100;
          status () << "Using the treshold of " << treshold << " out of " << SSA_steps_size << " SSA steps\n";
          status () << "Assuming a timeout of " << (impl_timeout/1000) << "." << (impl_timeout%1000)/10 << " seconds." << eom;
    }

  void do_it(partitioning_target_equationt &equation);
  void do_it(smt_symex_target_equationt &equation);

  using SSA_stepst = std::vector<symex_target_equationt::SSA_stept*> ;
  using SSA_steps_it = SSA_stepst::iterator;

  void find_var_deps(UnionFind<std::string> &deps_ds, std::map<std::string, bool> &visited);
  void find_assert_deps();
  virtual long find_implications()=0;

#ifdef DISABLE_OPTIMIZATIONS   
  void print_SSA_steps_infos();
  void print_SSA_steps(); 
  void print_expr_operands(std::ostream &out, exprt expr, int indent);
#endif
  void get_expr_symbols(const exprt &expr, symbol_sett& symbols);
  void print_expr_symbols(std::ostream &out, exprt expr);
  void print_expr_symbols(std::ostream &out, symbol_sett& s);
  std::string variable_name(std::string name);
  std::string variable_name(dstringt name);
  void print_dependents(std::map<std::string,bool> dependents, std::ostream &out);

  virtual std::pair<bool, fine_timet> check_implication(SSA_steps_it c1, SSA_steps_it c2)=0;
  bool compare_assertions(std::size_t idx1, std::size_t idx2);

protected:
  const goto_programt &goto_program;
  const namespacet &ns;
  ui_message_handlert &message_handler;
  subst_scenariot &omega;

  int last_label;
  std::map<std::string,int*> label;
  //std::map<std::string,std::map<std::string,bool> > var_deps;
  std::map<std::size_t,std::map<std::size_t,bool> > assert_deps;
  std::map<std::size_t,std::map<std::size_t,bool> > assert_imps;
//  std::map<SSA_steps_it,bool> toCheck;

  /* Contain indices to SSA_steps */
  std::vector<std::size_t> asserts;
//  std::map<std::string,int> instances;
  unsigned treshold;

  SSA_stepst SSA_steps; // similar stuff to what symex_target_equationt has
  std::map<exprt, exprt> SSA_map;
//  std::vector<std::string> equation_symbols;
  unsigned long impl_timeout;
  
  void reconstruct_exec_SSA_order(partitioning_target_equationt &equation);
};

extern inline bool operator<(
  const dependency_checkert::SSA_stepst::const_iterator a,
  const dependency_checkert::SSA_stepst::const_iterator b)
{
  return &(*a)<&(*b);
}

extern inline bool operator==(
    symex_target_equationt::SSA_stept a,
    symex_target_equationt::SSA_stept b)
{
  return a.source.pc == b.source.pc;
}
#endif
