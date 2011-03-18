/*******************************************************************\

Module: Propositional interpolant.  Based on code of cnft.

Author: Ondrej Sery

\*******************************************************************/
#include <limits.h>
#include "prop_itp.h"

/*******************************************************************\

Function: prop_itpt::gate_and

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void prop_itpt::gate_and(literalt a, literalt b, literalt o)
{
  // a*b=c <==> (a + o')( b + o')(a'+b'+o)
  bvt lits;

  lits.clear();
  lits.reserve(2);
  lits.push_back(pos(a));
  lits.push_back(neg(o));
  clauses.push_back(lits);

  lits.clear();
  lits.reserve(2);
  lits.push_back(pos(b));
  lits.push_back(neg(o));
  clauses.push_back(lits);

  lits.clear();
  lits.reserve(3);
  lits.push_back(neg(a));
  lits.push_back(neg(b));
  lits.push_back(pos(o));
  clauses.push_back(lits);
}

/*******************************************************************\

Function: prop_itpt::gate_or

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void prop_itpt::gate_or(literalt a, literalt b, literalt o)
{
  // a+b=c <==> (a' + c)( b' + c)(a + b + c')
  bvt lits;

  lits.clear();
  lits.reserve(2);
  lits.push_back(neg(a));
  lits.push_back(pos(o));
  clauses.push_back(lits);

  lits.clear();
  lits.reserve(2);
  lits.push_back(neg(b));
  lits.push_back(pos(o));
  clauses.push_back(lits);

  lits.clear();
  lits.reserve(3);
  lits.push_back(pos(a));
  lits.push_back(pos(b));
  lits.push_back(neg(o));
  clauses.push_back(lits);
}

/*******************************************************************\

Function: prop_itpt::land

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt prop_itpt::land(literalt a, literalt b)
{
  if(a==const_literal(true)) return b;
  if(b==const_literal(true)) return a;
  if(a==const_literal(false)) return const_literal(false);
  if(b==const_literal(false)) return const_literal(false);
  if(a==b) return a;

  literalt o=new_variable();
  gate_and(a, b, o);
  return o;
}

/*******************************************************************\

Function: cnft::lor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt prop_itpt::lor(literalt a, literalt b)
{
  if(a==const_literal(false)) return b;
  if(b==const_literal(false)) return a;
  if(a==const_literal(true)) return const_literal(true);
  if(b==const_literal(true)) return const_literal(true);
  if(a==b) return a;

  literalt o=new_variable();
  gate_or(a, b, o);
  return o;
}

/*******************************************************************\

Function: prop_itpt::lnot

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt prop_itpt::lnot(literalt a)
{
  a.invert();
  return a;
}

/*******************************************************************\

Function: prop_itpt::generalize

  Inputs:

 Outputs:

 Purpose: Renames propositional variables so that the interpolant is
 no longer dependent on the original symbols but only on their
 order.

\*******************************************************************/

void prop_itpt::generalize(const prop_convt& decider,
    const std::vector<symbol_exprt>& symbols)
{
  if (is_trivial()) {
    return;
  }

  // FIXME: Dirty cast.
  const boolbv_mapt::mappingt& mapping =
          dynamic_cast<const boolbvt&>(decider).get_literal_map().mapping;

  unsigned min_var = UINT_MAX;
  unsigned max_var = 0;
  // Get the bounds first
  for (std::vector<symbol_exprt>::const_iterator it = symbols.begin();
          it != symbols.end();
          ++it) {
    boolbv_mapt::mappingt::const_iterator pos = mapping.find(
            it->get_identifier());

    if (pos == mapping.end()) {
      // Bool symbols are not in the boolbv_map and have to be treated separatelly
      if (it->type().id() == ID_bool) {
        literalt l;
        if (!decider.literal(*it, l)) {
          unsigned var_no = l.var_no();

          std::cout << " -> '" << it->get_identifier().as_string() <<
                  "' - bool (" << var_no << ")" << std::endl;

          if (min_var > var_no) min_var = var_no;
          if (max_var < var_no) max_var = var_no;
        }
      }
      continue;
    }
    const boolbv_mapt::map_entryt& entry = pos->second;
    
    std::cout << " -> '" << it->get_identifier().as_string() << "' - " << entry.width << std::endl;

    for (boolbv_mapt::literal_mapt::const_iterator it2 = entry.literal_map.begin();
            it2 != entry.literal_map.end();
            ++it2) {
      if (!it2->is_set) continue;
      
      unsigned var_no = it2->l.var_no();
      
      if (min_var > var_no) min_var = var_no;
      if (max_var < var_no) max_var = var_no;
    }
  }
  assert (min_var < UINT_MAX && max_var > 0);
  
  unsigned renaming[max_var - min_var + 1];
  std::cout << " = " << min_var << " - " << max_var << std::endl;

#ifndef NDEBUG
  for (unsigned i = 0; i < max_var - min_var + 1; ++i)
    renaming[i] = UINT_MAX;
#endif

  // Fill the renaming table
  unsigned cannon_var_no = 1;
  for (std::vector<symbol_exprt>::const_iterator it = symbols.begin();
          it != symbols.end();
          ++it) {
    boolbv_mapt::mappingt::const_iterator pos = mapping.find(
            it->get_identifier());
    if (pos == mapping.end()) {
      // Bool symbols are not in the boolbv_map and have to be treated separatelly
      if (it->type().id() == ID_bool) {
        literalt l;
        if (!decider.literal(*it, l)) {
          // NOTE: We assume that the variables are unsigned and there are
          // no duplicates. This migh not hold if some optimizations are added
          // to the flattening process
          assert (!l.sign());
          // TODO: We need unique prop. variables only for the input parameters,
          // if there is duplication among output variables (due to unification
          // in symex), we just need to explicitly assert the unification by
          // adding new clauses.
          assert (renaming[l.var_no() - min_var] == UINT_MAX);

          renaming[l.var_no() - min_var] = cannon_var_no++;

          std::cout << l.var_no() << " ";
        }
      }
      continue;
    }
    const boolbv_mapt::map_entryt& entry = pos->second;

    for (boolbv_mapt::literal_mapt::const_iterator it2 = entry.literal_map.begin();
            it2 != entry.literal_map.end();
            ++it2) {
      if (!it2->is_set) {
        std::cout << "- ";
        continue;
      }

      // NOTE: We assume that the variables are unsigned and there are
      // no duplicates. This migh not hold if some optimizations are added
      // to the flattening process
      assert (!it2->l.sign());
      assert (renaming[it2->l.var_no() - min_var] == UINT_MAX);
      
      renaming[it2->l.var_no() - min_var] = cannon_var_no++;

      std::cout << it2->l.var_no() << " ";
    }
    std::cout << std::endl;
  }

  std::cout << "Renaming:" << std::endl;
  for (unsigned i = 0; i < max_var - min_var + 1; ++i) {
    if (i % 16 == 0) {
      if (i != 0) std::cout << std::endl;
    } else {
      std::cout << " ";
    }
    std::cout << (renaming[i] == UINT_MAX ? -1 : (int)renaming[i]);
  }

  std::cout << "Before generalization: " << std::endl;
  print(std::cout);

  // Do the renaming itself
  unsigned shift = _no_orig_variables - cannon_var_no;
  for (clausest::iterator it = clauses.begin();
          it != clauses.end();
          ++it) {
    for (bvt::iterator it2 = it->begin();
            it2 != it->end();
            ++it2) {

      // Only shift the artifitial variables (present due to the Tseitin
      // encoding to CNF)
      if (it2->var_no() > max_var) {
        it2->set(it2->var_no() - shift, it2->sign());
        continue;
      }

      // Sanity check, all variables used in the interpolant should be mapped.
      assert(renaming[it2->var_no() - min_var] != UINT_MAX);

      it2->set(renaming[it2->var_no() - min_var], it2->sign());
    }
  }
  if (root_literal.var_no() > max_var) {
    root_literal.set(root_literal.var_no() - shift, root_literal.sign());
  } else {
      // Sanity check, all variables used in the interpolant should be mapped.
      assert(renaming[root_literal.var_no() - min_var] != UINT_MAX);
      root_literal.set(renaming[root_literal.var_no() - min_var], root_literal.sign());
  }

  _no_variables -= shift;
  _no_orig_variables = cannon_var_no;

  // TODO: Should we force mapping of common symbols to fresh prop. variables
  // in order to prevent unification?

  std::cout << "After generalization: " << std::endl;
  print(std::cout);
}


/*******************************************************************\

Function: prop_itpt::substitute

  Inputs:

 Outputs:

 Purpose: Renames propositional variables so that the interpolant is
 valid for the given set of identifiers. Moreover, the interpolant is
 asserted in the given propositional solver.

\*******************************************************************/

void prop_itpt::substitute(prop_convt& decider,
    const std::vector<symbol_exprt>& symbols) const
{
  assert(!is_trivial());

  // FIXME: Dirty cast.
  boolbv_mapt& map = dynamic_cast<boolbvt&>(decider).get_literal_map();
  literalt renaming[_no_variables];

  // Fill the renaming table
  unsigned cannon_var_no = 1;
  for (std::vector<symbol_exprt>::const_iterator it = symbols.begin();
          it != symbols.end();
          ++it) {

    // Bool symbols are not in the boolbv_map and have to be treated separatelly
    if (it->type().id() == ID_bool) {
      literalt l = decider.convert(*it);
      renaming[cannon_var_no++] = l;
      std::cout << (l.sign() ? "-" : "") << l.var_no() << " ";
      continue;
    }

    for (unsigned i = 0;
            i < map.get_map_entry(it->get_identifier(), it->type()).width;
            ++i) {
      literalt l = map.get_literal(it->get_identifier(), i, it->type());

      renaming[cannon_var_no++] = l;
      std::cout << (l.sign() ? "-" : "") << l.var_no() << " ";
    }
    std::cout << std::endl;
  }

  // Allocate new variables for the auxiliary ones (present due to the Tseitin
  // encoding to CNF)
  for (unsigned i = _no_orig_variables; i < _no_variables; ++i) {
    renaming[i] = decider.prop.new_variable();
  }

  // Rename and output the clauses
  bvt tmp_clause;
  for (clausest::const_iterator it = clauses.begin();
          it != clauses.end();
          ++it) {
    tmp_clause = *it;

    for (bvt::iterator it2 = tmp_clause.begin();
            it2 != tmp_clause.end();
            ++it2) {
      // Rename
      bool sign = it2->sign();
      *it2 = renaming[it2->var_no()];
      if (sign)
        it2->invert();
    }
    
    print_clause(std::cout, tmp_clause);
    std::cout << std::endl;

    // Assert the clause
    decider.prop.lcnf(tmp_clause);
  }
  // Handle the root
  bool sign = root_literal.sign();
  literalt new_root_literal = renaming[root_literal.var_no()];
  if (sign)
    new_root_literal.invert();

  decider.prop.l_set_to_true(new_root_literal);
}


/*******************************************************************\

Function: prop_itpt::substitute

  Inputs:

 Outputs:

 Purpose: Forces the given decider to use fresh variables for
 the partition (future interpolant) boundary.

\*******************************************************************/

void prop_itpt::reserve_variables(prop_convt& decider,
    const std::vector<symbol_exprt>& symbols)
{
  // FIXME: Dirty cast.
  boolbv_mapt& map = dynamic_cast<boolbvt&>(decider).get_literal_map();

  // Force existence of the variables
  for (std::vector<symbol_exprt>::const_iterator it = symbols.begin();
          it != symbols.end();
          ++it) {

    // Bool symbols are not in the boolbv_map and have to be treated separatelly
    if (it->type().id() == ID_bool) {
      literalt l = decider.convert(*it);
      continue;
    }

    for (unsigned i = 0;
            i < map.get_map_entry(it->get_identifier(), it->type()).width;
            ++i) {
      literalt l = map.get_literal(it->get_identifier(), i, it->type());
    }
  }
}

/*******************************************************************\

Function: prop_itpt::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void prop_itpt::print(std::ostream& out) const
{
  if (is_trivial()) {
    out << "Prop. interpolant: trivial" << std::endl;
  } else {
    out << "Prop. interpolant (#v: " << _no_variables << ", #c: " << no_clauses() <<
            ",root: " << root_literal.dimacs() << "):" << std::endl;

#   if 0
    for (clausest::const_iterator it = clauses.begin();
            it != clauses.end(); ++it) {
      print_clause(out, *it);
      out << std::endl;
    }
#   endif
  }
}

/*******************************************************************\

Function: prop_itpt::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void prop_itpt::print_clause(std::ostream& out, const bvt& clause) const {
  for (bvt::const_iterator it2 = clause.begin();
          it2 != clause.end(); ++it2) {
    if (it2 != clause.begin())
      out << " ";
    out << it2->dimacs();
  }
}
