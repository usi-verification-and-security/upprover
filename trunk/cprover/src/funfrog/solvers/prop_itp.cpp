/*******************************************************************\

Module: Propositional interpolant.  Based on code of cnft.

Author: Ondrej Sery

\*******************************************************************/

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

Function: prop_itpt::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void prop_itpt::print(std::ostream& out) const
{
  out << "Prop. interpolant (#vars: " << _no_variables << ", #clauses: " << no_clauses() << "):" << std::endl;
  
  for (clausest::const_iterator it = clauses.begin();
          it != clauses.end(); ++it) {
    for (bvt::const_iterator it2 = it->begin();
            it2 != it->end(); ++it2) {
      if (it2 != it->begin())
        out << " ";
      out << it2->dimacs();
    }
    out << std::endl;
  }
}
