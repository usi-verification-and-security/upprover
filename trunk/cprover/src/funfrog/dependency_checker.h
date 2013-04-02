#ifndef CPROVER_DEPENDECY_CHECKER_H
#define CPROVER_DEPENDECY_CHECKER_H

#include <queue>

#include <goto-programs/goto_program.h>
#include <solvers/flattening/sat_minimizer.h>

#include <namespace.h>
#include <symbol.h>
#include <ui_message.h>

#include <base_type.h>
#include <time_stopping.h>

#include "partitioning_target_equation.h"
#include "partitioning_slice.h"
#include "subst_scenario.h"

#include <map>

using namespace std;

class dependency_checkert : public messaget
{
public:
    dependency_checkert(
          const namespacet &_ns,
          partitioning_target_equationt &_target,
          ui_message_handlert &_message_handler,
          const goto_programt &_goto_program,
          subst_scenariot &_omega,
          //int percentage
          int fraction
    ) :
          goto_program(_goto_program),
          ns(_ns),
          message_handler (_message_handler),
          equation(_target),
          omega(_omega)
    {
          set_message_handler(_message_handler);
          last_label = 0;
          impl_timeout = 2000;
          // FIXME: make treshold parametrized
          treshold = equation.SSA_steps.size() / fraction;
          //treshold = percentage * equation.SSA_steps.size() / 100;
          std::cout << "Using the treshold of " << treshold << " out of " << equation.SSA_steps.size() << " SSA steps\n";
          std::cout << "Assuming a timeout of " << time2string(impl_timeout) << endl;
    }

  void do_it();

  typedef symex_target_equationt::SSA_stepst::iterator SSA_step_reft;
  void find_var_deps(bool ENABLE_TC=0);
  void find_assert_deps();
  fine_timet find_implications();
  void get_minimals();

  void print_SSA_steps_infos();
  void print_SSA_steps();
  void print_expr_operands(ostream &out, exprt expr, int indent);
  void get_expr_symbols(const exprt &expr, symbol_sett& symbols);
  void print_expr_symbols(ostream &out, exprt expr);
  void print_expr_symbols(ostream &out, symbol_sett& s);
  string variable_name(string name);
  string variable_name(dstring name);
  void print_dependents(map<string,bool> dependents, ostream &out);

  pair<bool, fine_timet> check_implication(SSA_step_reft &c1, SSA_step_reft &c2);
  bool compare_assertions(SSA_step_reft &a, SSA_step_reft &b);

private:
  const goto_programt &goto_program;
  const namespacet &ns;
  ui_message_handlert &message_handler;

  partitioning_target_equationt &equation;
  subst_scenariot &omega;

  int last_label;
  map<string,int*> label;
  map<string,map<string,bool> > var_deps;
  map<SSA_step_reft,map<SSA_step_reft,bool> > assert_deps;
  map<SSA_step_reft,map<SSA_step_reft,bool> > assert_imps;
  map<SSA_step_reft,bool> toCheck;

  vector<SSA_step_reft> asserts;
  unsigned treshold;

  fine_timet impl_timeout;

  void convert_delta_SSA(prop_convt &prop_conv, SSA_step_reft &it1, SSA_step_reft &it2);
  void convert_assignments(prop_convt &prop_conv, SSA_step_reft &it1, SSA_step_reft &it2);
  void convert_assumptions(prop_convt &prop_conv, SSA_step_reft &it1, SSA_step_reft &it2);
  void convert_assertions(prop_convt &prop_conv, SSA_step_reft &it2);
  void convert_guards(prop_convt &prop_conv, SSA_step_reft &it1, SSA_step_reft &it2);
  void convert_io(prop_convt &prop_conv, SSA_step_reft &it1, SSA_step_reft &it2);

};
#endif
