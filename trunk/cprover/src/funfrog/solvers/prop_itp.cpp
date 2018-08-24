/*******************************************************************\

Module: Propositional interpolant.  Based on code of cnft.

Author: Ondrej Sery

\*******************************************************************/
#include "prop_itp.h"
#include <iostream>

//#define DEBUG_ITP


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
    out << "Prop. interpolant (#v: " << _no_variables << ", #c: " << clauses.size() <<
            ",root: " << root_literal.dimacs() << "):" << std::endl;

#   ifdef DEBUG_ITP
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

/*******************************************************************\

Function: prop_itpt::serialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void prop_itpt::serialize(std::ostream& out) const
{
  out << _no_orig_variables << " ";
  out << _no_variables << " ";
  out << root_literal.get() << " ";
  out << clauses.size() << std::endl;
  out << symbol_mask.size() << std::endl;

  for (std::vector<bool>::const_iterator it = symbol_mask.begin();
          it != symbol_mask.end();
          ++it) {
    out << (*it ? '1' : '0');
  }
  out << std::endl;
    
  for (clausest::const_iterator it = clauses.begin();
          it != clauses.end();
          ++it) {
    out << it->size();

    for (bvt::const_iterator it2 = it->begin();
            it2 != it->end();
            ++it2) {
      out << " " << it2->get();
    }
    out << std::endl;
  }
}

/*******************************************************************\

Function: prop_itpt::deserialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void prop_itpt::deserialize(std::istream& in)
{
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
}

bool prop_itpt::equals(itpt * other) const {
    // TODO: how to effectively find if two propositional summaries are the same?
    return false;
}

