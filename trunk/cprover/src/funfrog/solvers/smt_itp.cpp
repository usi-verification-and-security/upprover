#include <algorithm>
#include <limits.h>
#include <string.h>
#include "smt_itp.h"
#include <stdlib.h>
#include <iostream>
#include "smtcheck_opensmt2.h"

//#define DEBUG_ITP

bool
smt_itpt::usesVar(symbol_exprt& symb, unsigned idx)
{
    assert(tterm != NULL && logic != NULL);

    string _var_name = id2string(symb.get_identifier());
    string var_name = smtcheck_opensmt2t::remove_invalid(_var_name);
    var_name = smtcheck_opensmt2t::remove_index(var_name);
    var_name = smtcheck_opensmt2t::quote_varname(var_name);
    const vec<PTRef>& args = tterm->getArgs();
    for(int i = 0; i < args.size(); ++i)
    {
        string pname = logic->getSymName(args[i]);
        pname = smtcheck_opensmt2t::remove_index(pname);
        pname = smtcheck_opensmt2t::quote_varname(pname);
        if(pname == var_name) return true;
    }
    return false;
}


/*******************************************************************\

Function: smt_itpt::gate_and

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt_itpt::gate_and(literalt a, literalt b, literalt o)
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

Function: smt_itpt::gate_or

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt_itpt::gate_or(literalt a, literalt b, literalt o)
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

Function: smt_itpt::land

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt smt_itpt::land(literalt a, literalt b)
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

literalt smt_itpt::lor(literalt a, literalt b)
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

Function: smt_itpt::lnot

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt smt_itpt::lnot(literalt a)
{
  a.invert();
  return a;
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

# ifdef DEBUG_ITP
  std::cout << "--------------- Generalizing -------------" << std::endl;
# endif

 // TODO: Re-write the code for SMT (see the Prop version)
}


/*******************************************************************\

Function: smt_itpt::substitute

  Inputs:

 Outputs:

 Purpose: Renames propositional variables so that the interpolant is
 valid for the given set of identifiers. Moreover, the interpolant is
 asserted in the given propositional solver.

\*******************************************************************/

void smt_itpt::substitute(smtcheck_opensmt2t& decider,
    const std::vector<symbol_exprt>& symbols,
    bool inverted) const
{
    assert(!is_trivial());
    assert(tterm && logic);
    const vec<PTRef>& args = tterm->getArgs();
    Map<PTRef, PtAsgn, PTRefHash> subst;

    map<string, int[3]> occurrences;
    for(int i = 0; i < symbols.size(); ++i)
    {
        string fixed_str = id2string(symbols[i].get_identifier());
        string unidx = smtcheck_opensmt2t::remove_index(fixed_str);
        if(occurrences.find(unidx) == occurrences.end())
        {
            occurrences[unidx][0] = 1;
            occurrences[unidx][1] = smtcheck_opensmt2t::get_index(fixed_str);
        }
        else
        {
            ++occurrences[unidx][0];
            assert(occurrences[unidx][0] == 2);
            int new_idx = smtcheck_opensmt2t::get_index(fixed_str);
            int old_idx = occurrences[unidx][1];
            if(new_idx < old_idx) std::swap(new_idx, old_idx);
            occurrences[unidx][1] = old_idx;
            occurrences[unidx][2] = new_idx;
        }

    }

    for(int i = 0; i < symbols.size(); ++i)
    {
        string fixed_str = id2string(symbols[i].get_identifier());
        string unidx = smtcheck_opensmt2t::remove_index(fixed_str);
        string quoted_unidx = smtcheck_opensmt2t::quote_varname(unidx);
        int idx = smtcheck_opensmt2t::get_index(fixed_str);
        for(int j = 0; j < args.size(); ++j)
        {
            string aname = string(logic->getSymName(args[j]));
            string unidx_aname = smtcheck_opensmt2t::remove_index(aname);
            string quoted_unidx_aname = smtcheck_opensmt2t::quote_varname(unidx_aname);
            if(quoted_unidx == quoted_unidx_aname)
            {
                if( (occurrences[unidx][0] == 1) ||
                        (idx == occurrences[unidx][1] && aname.find("#in") != string::npos) ||
                     (idx == occurrences[unidx][2] && aname.find("#out") != string::npos)
                  )
                {
                    //cout << "VAR " << logic->printTerm(args[j]) << " WILL BE " << fixed_str << endl;
                    //literalt l = decider.convert(symbols[i]);
                    //PTRef tmp = decider.literal2ptref(l);
        	        PTRef tmp = decider.convert_symbol(symbols[i]);
                    subst.insert(args[j], PtAsgn(tmp, l_True));
                }
            }
        }
    }
    PTRef part_sum;
    PTRef templ = tterm->getBody();
    logic->varsubstitute(templ, subst, part_sum);
    decider.set_to_true(part_sum);
    //cout << "; Template instantiated for function " << tterm->getName() << " is\n" << logic->printTerm(part_sum) << endl;

  /*
  // FIXME: Dirty cast.
  boolbv_mapt& map = const_cast<boolbv_mapt&>(dynamic_cast<boolbvt&>(decider).get_map());
  literalt* renaming = new literalt[_no_variables];

# ifdef DEBUG_ITP
  std::cout << "--------------- Substituting -------------" << std::endl;
# endif
  
  // Fill the renaming table
  unsigned cannon_var_no = 1;
  for (std::vector<symbol_exprt>::const_iterator it = symbols.begin();
          it != symbols.end();
          ++it) {

    // Bool symbols are not in the boolbv_map and have to be treated separatelly
    if (it->type().id() == ID_bool) {
      literalt l = decider.convert(*it);
      
#     ifdef DEBUG_ITP
      std::cout << (l.sign() ? "-" : "") << l.var_no() << " ";
      std::cout << it->get_identifier().c_str() << " (1)" << std::endl;
#     endif
      assert(cannon_var_no < _no_variables);
      renaming[cannon_var_no++] = l;
      continue;
    }

#   ifdef DEBUG_ITP
    std::cout << it->get_identifier().c_str() << " (" << 
            map.get_map_entry(it->get_identifier(), it->type()).width <<
            ")" << std::endl;
#   endif
    bvt literals;
    const unsigned width = map.get_map_entry(it->get_identifier(), it->type()).width;
    literals.resize(width);
    map.get_literals(
      it->get_identifier(), it->type(), width, literals);
    for (unsigned i = 0; i < width; ++i) {
      literalt l = literals[i];
#     ifdef DEBUG_ITP
      std::cout << (l.sign() ? "-" : "") << l.var_no() << " ";
#     endif
      assert(cannon_var_no < _no_variables);
      renaming[cannon_var_no++] = l;
    }
#   ifdef DEBUG_ITP
    std::cout << std::endl;
#   endif
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
      if (sign){
       it2->invert();
      }
    }
    // Assert the clause
    decider.prop.lcnf(tmp_clause);
  }

  // Handle the root
  bool sign = root_literal.sign();
  literalt new_root_literal = renaming[root_literal.var_no()];
  if (sign)
    new_root_literal.invert();
  
  if (inverted)
    new_root_literal.invert();

  decider.prop.l_set_to_true(new_root_literal);

  delete [] renaming;
  */
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

#   ifdef DEBUG_ITP
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
    out << "Prop. interpolant: trivial" << std::endl;
  } else {
    out << "Prop. interpolant (#v: " << _no_variables << ", #c: " << clauses.size() <<
            ",root: " << root_literal.dimacs() << "):" << std::endl;

// KE: Old code with bv only, need to be re-write for SMT
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
    assert(logic && tterm);
    logic->dumpFunction(out, *tterm);
    return; 

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

Function: smt_itpt::deserialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt_itpt::deserialize(std::istream& in)
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
