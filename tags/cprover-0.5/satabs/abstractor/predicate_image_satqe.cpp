/*******************************************************************\

Module: Predicate Abstraction of a Basic Block

Author: Daniel Kroening, kroening@kroening.com
        Stefano Tonetta, tonettas@lu.unisi.ch

\*******************************************************************/

#include <i2string.h>
#include <std_expr.h>
#include <expr_util.h>

#include <solvers/flattening/bv_pointers.h>
#include <satqe/satqe_satcheck.h>

#include "predabs_aux.h"
#include "predicate_image_satqe.h"

/*******************************************************************\

Function: predicate_image_satqe

  Inputs:

 Outputs:

 Purpose: It feeds zChaff with equation and gets back a set of
          cubes that represent the solutions of the SAT instance
          projected on the predicates. It translates the cubes into
          an expression and stores it as constraint of the abstract
          transition relation.

\*******************************************************************/

void predicate_image_satqe(
  message_handlert &message_handler,
  const std::vector<exprt> &deref_curr_predicates,
  const std::vector<exprt> &deref_next_predicates,
  const std::list<exprt> &constraints,
  symex_target_equationt &equation,
  const namespacet &ns,
  abstract_transition_relationt &
  abstract_transition_relation)
{
  const std::set<unsigned> &from_predicates=
    abstract_transition_relation.from_predicates;

  const std::set<unsigned> &to_predicates=
    abstract_transition_relation.to_predicates;

  assert(to_predicates.size()!=0);

  // create SAT solver object
  satqe_satcheckt satqe;
  bv_pointerst solver(satqe);

  solver.unbounded_array=boolbvt::U_ALL;
  solver.set_message_handler(message_handler);

  // turn equation into CNF
  equation.convert(solver);
  
  for(std::set<unsigned>::const_iterator
      it=from_predicates.begin();
      it!=from_predicates.end();
      it++)
  {
    unsigned i=*it;

    literalt li=make_pos(ns, solver, deref_curr_predicates[i]);
    satqe.quantify(li);
  }

  for(std::set<unsigned>::const_iterator
      it=to_predicates.begin();
      it!=to_predicates.end();
      it++)
  {
    unsigned i=*it;

    literalt lo=make_pos(ns, solver, deref_next_predicates[i]);
    satqe.quantify(lo);
  }

  // we want cubes
  cube_sett cube_set;
  satqe.set_cube_set(cube_set);

  // solve it
  switch(solver.dec_solve())
  {
   case decision_proceduret::D_UNSATISFIABLE:
    // OK, this is what we expect
    break;

   default:
    throw "unexpected result from satqe.solve()";
  }

  message_handler.print(9, "Generated "+
    i2string(cube_set.no_insertions())+" cube(s)");

  #if 0
  std::cout << cube_set;
  #endif

  exprt constraint_cubes_disj = true_exprt();

  // convert the cubes into constraints
  for(cubest::star_mapt::const_iterator
      it=cube_set.star_map.begin();
      it!=cube_set.star_map.end();
      it++)
  {
    for(cubest::bitssett::const_iterator
        it2=it->second.begin();
        it2!=it->second.end();
        it2++)
    {
      exprt constraint_cube_conj;

      unsigned bit=0;
      unsigned i=0;

      /* Assume it->first[i] is true iff the i-th predicate is in the
	 cube. Assume predicates are stored in it->first in the order of
	 from_predicates followed by to_predicates. Scan it->first and
	 from/to_predicates in parallel to get the cube. */

      for(std::set<unsigned>::const_iterator
          it3=from_predicates.begin();
          it3!=from_predicates.end();
          it3++)
      {
        unsigned id=*it3;
        
        if(!it->first[i])
        {
          constraint_cube_conj.operands().push_back(exprt());
          exprt &e=constraint_cube_conj.operands().back();
          e=exprt("predicate_symbol", typet("bool"));
          e.set("identifier", id);

          if(!(*it2)[bit]) 
            e.make_not();

          bit++;
          #if 0
          std::cout << "C: " << from_expr(ns, "", e) << std::endl;
          #endif
        }
          
        i++;
      }

      for(std::set<unsigned>::const_iterator
          it3=to_predicates.begin();
          it3!=to_predicates.end();
          it3++)
      {
        unsigned id=*it3;

        if(!it->first[i])
        {
          constraint_cube_conj.operands().push_back(exprt());
          exprt &e=constraint_cube_conj.operands().back();
          e=exprt("predicate_next_symbol", typet("bool"));
          e.set("identifier", id);

          if(!(*it2)[bit]) 
            e.make_not();

          bit++;
          #if 0
          std::cout << "C: " << from_expr(ns, "", e) << std::endl;
          #endif
        }

        i++;
      }

      assert(i==it->first.size());

      /* Convert the cube into a conjunct. */
      gen_and(constraint_cube_conj);

      /* Add the conjunct in disjunction to previous cubes. */
      if(constraint_cubes_disj.is_true())
	constraint_cubes_disj=constraint_cube_conj;
      else
	constraint_cubes_disj=gen_or(
	  constraint_cubes_disj,
	  constraint_cube_conj);      
    }
  }

  /* Add the cubes to the contraints of the abstract transition
     relation. Warning: we may want to remove old constrains. */

  abstract_transition_relation.constraints.push_back(constraint_cubes_disj);
}
