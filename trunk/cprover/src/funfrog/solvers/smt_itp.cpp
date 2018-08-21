/*******************************************************************\

Module: SMT interpolant.  Based on code on prop_itp.

Author: 

\*******************************************************************/

#include "smt_itp.h"
#include "../hifrog.h"
#include "../utils/naming_helpers.h"

//#define DEBUG_ITP_SMT
# ifdef DEBUG_ITP_SMT
#include <iostream>
#endif

bool
smt_itpt::usesVar(symbol_exprt& symb, unsigned idx)
{
    // TODO unify with prop, maybe store names of the arguments and flags which are actually used
    return true;
}

/*******************************************************************\

Function: smt_itpt::generalize

  Inputs:

 Outputs:

 Purpose: Renames propositional variables so that the interpolant is
 no longer dependent on the original symbols but only on their
 order.

\*******************************************************************/

void smt_itpt::generalize(const prop_conv_solvert& mapping,
    const std::vector<symbol_exprt>& symbols)
{
  symbol_mask.clear();
  if (is_trivial()) {
    return;
  }

# ifdef DEBUG_ITP_SMT
  std::cout << "--------------- Generalizing -------------" << std::endl;
# endif

 // TODO: Re-write the code for SMT (see the Prop version)
}


/*******************************************************************\

Function: smt_itpt::raw_assert

  Inputs:

 Outputs:

 Purpose: Asserts the encoding of the interpolant and returns the root
 literal. Fresh variables are used for auxiliary variables, but 
 the "interface" variables are used as they are. This is to be used for
 interpolant comparison.

\*******************************************************************/

literalt smt_itpt::raw_assert(propt& prop_decider) const
{
  assert(!is_trivial());


  // No stack allocation
  literalt* renaming =
    (literalt*)malloc(sizeof(literalt)*(_no_variables - _no_orig_variables));
//  literalt renaming[_no_variables - _no_orig_variables];

  // Make sure, the original variables are allocated
  while (prop_decider.no_variables() < _no_orig_variables) {
    prop_decider.new_variable();
  }
  // Allocate new variables for the auxiliary ones (present due to the Tseitin
  // encoding to CNF)
  for (unsigned i = 0; i < _no_variables - _no_orig_variables; ++i) {
    renaming[i] = prop_decider.new_variable();
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
      if (it2->var_no() >= _no_orig_variables) {
        // Rename
        bool sign = it2->sign();
        *it2 = renaming[it2->var_no() - _no_orig_variables];
        if (sign)
          it2->invert();
      }
    }

#   ifdef DEBUG_ITP_SMT
    print_clause(std::cout, tmp_clause);
    std::cout << std::endl;
#   endif

    // Assert the clause
    prop_decider.lcnf(tmp_clause);
  }
  // Handle the root
  literalt rval;
  if (root_literal.var_no() < _no_orig_variables)
    rval = root_literal;
  else {
    bool sign = root_literal.sign();
    literalt new_root_literal = 
            renaming[root_literal.var_no() - _no_orig_variables];
    if (sign)
      new_root_literal.invert();

    rval = new_root_literal;
  }
  free(renaming);
  return rval;
}

/*******************************************************************\

Function: smt_itpt::reserve_variables

  Inputs:

 Outputs:

 Purpose: Forces the given decider to use fresh variables for
 the partition (future interpolant) boundary.

\*******************************************************************/

void smt_itpt::reserve_variables(prop_conv_solvert& decider,
    const std::vector<symbol_exprt>& symbols, std::map<symbol_exprt, std::vector<unsigned> >& symbol_vars)
{
    // TODO: write for SMT. See the code in Prop version
    return; 
}

/*******************************************************************\

Function: smt_itpt::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt_itpt::print(std::ostream& out) const
{
    if (is_trivial()) {
        out << ";; SMT. interpolant: trivial" << std::endl;
    } else {
        out << ";; SMT. interpolant (#v: " 
            << _no_variables << ", #c: " << clauses.size() << ",root: "
            << root_literal.dimacs() << "):" << std::endl
            << m_decider->getPTermString(interpolant) << std::endl;
    }
}

/*******************************************************************\

Function: smt_itpt::serialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt_itpt::serialize(std::ostream& out) const
{
  assert(m_decider);
  m_decider->dump_function(out, templ);
}

/*******************************************************************\

Function: smt_itpt::deserialize

  Inputs:

 Outputs:

 Purpose: Not In USE

\*******************************************************************/

void smt_itpt::deserialize(std::istream& in)
{
  assert(0); // KE: when do we use it??
    
  unsigned raw_root;
  unsigned nclauses;
  unsigned nsymbols;

  in >> _no_orig_variables;
  in >> _no_variables;
  in >> raw_root;
  root_literal.set(raw_root);
  in >> nclauses;
  in >> nsymbols;

  if (in.fail())
    return;

  symbol_mask.clear();
  symbol_mask.reserve(nsymbols);
  
  for (unsigned i = 0; i < nsymbols; ++i) 
  {
    char ch;
    in >> ch;
    symbol_mask.push_back(ch == '1');
  }

  if (in.fail())
  return;

  unsigned lits;
  unsigned raw_lit;
  literalt lit;

  clauses.clear();
  clauses.reserve(nclauses);
  
  for (unsigned i = 0; i < nclauses; ++i)
  {
    in >> lits;

    if (in.fail())
      return;

    clauses.push_back(bvt());
    bvt& bv = clauses.back();
    bv.reserve(lits);

    for (unsigned j = 0; j < lits; ++j) {
      in >> raw_lit;
      lit.set(raw_lit);

      bv.push_back(lit);
    }
  }
} // NOT IN USE