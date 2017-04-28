#ifndef CPROVER_DEPENDECY_CHECKER_H
#define CPROVER_DEPENDECY_CHECKER_H

#include <goto-programs/goto_program.h>

#include <namespace.h>
#include <symbol.h>
#include <ui_message.h>

#include <base_type.h>
#include <time_stopping.h>
#include "partitioning_slice.h"
#include "subst_scenario.h"
#include "nopartition/smt_symex_target_equation.h"

#include <map>
#include <queue>

#include <boost/pending/disjoint_sets.hpp>

using namespace std;
using namespace boost;

#define INDEPT false
#define DEPT true

#define NOTIMP false
#define IMP true

#define VERBOSE false

#define IMIN(i, j) ((int)(i)<(int)(j))?(int)(i):(int)(j)
#define IMAX(i, j) ((int)(i)<(int)(j))?(int)(j):(int)(i)

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
          std::cout << "Using the treshold of " << treshold << " out of " << SSA_steps_size << " SSA steps\n";
          std::cout << "Assuming a timeout of " << (impl_timeout/1000) << "." << (impl_timeout%1000)/10 << " seconds." << std::endl;
    }

  void do_it(partitioning_target_equationt &equation);
  void do_it(smt_symex_target_equationt &equation);

  typedef std::list<symex_target_equationt::SSA_stept*> SSA_stepst;
  typedef SSA_stepst::iterator SSA_step_reft;

  typedef map<string, size_t> rank_t;
  typedef map<string, string> parent_t;

  typedef disjoint_sets<associative_property_map<rank_t>, associative_property_map<parent_t>, find_with_full_path_compression> str_disj_set;

  void find_var_deps(str_disj_set &deps_ds, map<string, bool> &visited, SSA_step_reft &it1, SSA_step_reft &it2);
  void find_assert_deps();
  virtual long find_implications()=0;
  void get_minimals();

  void print_SSA_steps_infos();
  void print_SSA_steps();
#ifdef DEBUG_SSA_PRINT  
  void print_expr_operands(ostream &out, exprt expr, int indent);
#endif
  void get_expr_symbols(const exprt &expr, symbol_sett& symbols);
  void print_expr_symbols(ostream &out, exprt expr);
  void print_expr_symbols(ostream &out, symbol_sett& s);
  string variable_name(string name);
  string variable_name(dstringt name);
  void print_dependents(map<string,bool> dependents, ostream &out);

  virtual pair<bool, fine_timet> check_implication(SSA_step_reft &c1, SSA_step_reft &c2)=0;
  bool compare_assertions(SSA_step_reft &a, SSA_step_reft &b);

protected:
  const goto_programt &goto_program;
  const namespacet &ns;
  ui_message_handlert &message_handler;
  subst_scenariot &omega;

  int last_label;
  map<string,int*> label;
  map<string,map<string,bool> > var_deps;
  map<SSA_step_reft,map<SSA_step_reft,bool> > assert_deps;
  map<SSA_step_reft,map<SSA_step_reft,bool> > assert_imps;
  map<SSA_step_reft,bool> toCheck;

  vector<SSA_step_reft> asserts;
  map<string,int> instances;
  unsigned treshold;

  SSA_stepst SSA_steps; // similar stuff to what symex_target_equationt has
  std::map<exprt, exprt> SSA_map;
  vector<string> equation_symbols;
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
