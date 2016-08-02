#include <limits.h>
#include <string.h>
#include "smt_itp.h"
#include <stdlib.h>
#include <iostream>
#include "smtcheck_opensmt2.h"

//#define DEBUG_ITP

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

void smt_itpt::generalize(const prop_convt& decider,
    const std::vector<symbol_exprt>& symbols)
{
  symbol_mask.clear();
  if (is_trivial()) {
    return;
  }

# ifdef DEBUG_ITP
  std::cout << "--------------- Generalizing -------------" << std::endl;
# endif

  // FIXME: Dirty cast.
  const boolbv_mapt::mappingt& mapping =
          dynamic_cast<const boolbvt&>(decider).get_map().mapping;

  unsigned min_var = UINT_MAX;
  unsigned max_var = 0;
  // Get the bounds first
  for (std::vector<symbol_exprt>::const_iterator it = symbols.begin();
          it != symbols.end();
          ++it) {
    boolbv_mapt::mappingt::const_iterator pos = mapping.find(
            it->get_identifier());

    if (pos == mapping.end()) {
      // Bool symbols are not in the boolbv_map and have to be treated separately
      if (it->type().id() == ID_bool) {
        literalt l;
        if (!decider.literal(*it, l)) {
          unsigned var_no = l.var_no();

#         ifdef DEBUG_ITP
          std::cout << " -> '" << it->get_identifier() <<
                  "' - bool (" << var_no << ")" << std::endl;
#         endif
          if (min_var > var_no) min_var = var_no;
          if (max_var < var_no) max_var = var_no;
        }
      }
      continue;
    }
    const boolbv_mapt::map_entryt& entry = pos->second;
    
#   ifdef DEBUG_ITP
    std::cout << " -> '" << it->get_identifier() << "' - " << entry.width << std::endl;
#   endif

   
    for (boolbv_mapt::literal_mapt::const_iterator it2 = entry.literal_map.begin();
            it2 != entry.literal_map.end();
            ++it2) {
      if (!it2->is_set)
        continue;

      unsigned var_no = it2->l.var_no();

      if (min_var > var_no) min_var = var_no;
      if (max_var < var_no) max_var = var_no;
    }
  }
  assert (min_var < UINT_MAX && max_var > 0);

# ifdef DEBUG_ITP
  std::cout << " = " << min_var << " - " << max_var << std::endl;
# endif
//  unsigned renaming[max_var - min_var + 1];
  unsigned* renaming = (unsigned*) malloc(sizeof(unsigned)*(max_var - min_var + 1));
//  unsigned represented_symbol[max_var - min_var + 1];
  unsigned* represented_symbol = (unsigned*)malloc(sizeof(unsigned)*(max_var - min_var + 1));

# ifndef NDEBUG
  // This is not exactly clean, but it should do for debugging purposes
  memset(renaming, UCHAR_MAX, sizeof(unsigned)*(max_var - min_var + 1));
  memset(represented_symbol, UCHAR_MAX, sizeof(unsigned)*(max_var - min_var + 1));
# endif
  
  // Fill the renaming table
  unsigned cannon_var_no = 1;
  unsigned current_symbol = 0;
  for (std::vector<symbol_exprt>::const_iterator it = symbols.begin();
          it != symbols.end();
          ++it, ++current_symbol) {
    boolbv_mapt::mappingt::const_iterator pos = mapping.find(
            it->get_identifier());
    if (pos == mapping.end()) {
      // Bool symbols are not in the boolbv_map and have to be treated separatelly
      if (it->type().id() == ID_bool) {
        literalt l;
#       ifdef DEBUG_ITP
        std::cout << it->get_identifier().c_str() << " (1)" << std::endl;
#       endif
        if (!decider.literal(*it, l)) {
          // NOTE: We assume that the variables are unsigned and there are
          // no duplicates. This migh not hold if some optimizations are added
          // to the flattening process
          assert (!l.sign());
          // TODO: We need unique prop. variables only for the input parameters,
          // if there is duplication among output variables (due to unification
          // in symex), we just need to explicitly assert the unification by
          // adding new clauses.
          unsigned idx = l.var_no() - min_var;
          assert (renaming[idx] == UINT_MAX);
          renaming[idx] = cannon_var_no;
          represented_symbol[idx] = current_symbol;

#         ifdef DEBUG_ITP
          std::cout << l.var_no() << " ";
#         endif
        }
      }
      cannon_var_no++;
      continue;
    }
    const boolbv_mapt::map_entryt& entry = pos->second;

#   ifdef DEBUG_ITP
    std::cout << it->get_identifier().c_str() << " (" << entry.width << ")" << std::endl;
#   endif
    for (boolbv_mapt::literal_mapt::const_iterator it2 = entry.literal_map.begin();
            it2 != entry.literal_map.end();
            ++it2) {
      if (!it2->is_set) {
#       ifdef DEBUG_ITP
        std::cout << "- ";
#       endif
        cannon_var_no++;
        continue;
      }

      // NOTE: We assume that the variables are unsigned and there are
      // no duplicates. This might not hold if some optimizations are added
      // to the flattening process
      unsigned idx = it2->l.var_no() - min_var;
      //assert (it2->l.var_no() >= min_var);
      //assert (!it2->l.sign());
      //assert (renaming[idx] == UINT_MAX);
      renaming[idx] = cannon_var_no++;
      represented_symbol[idx] = current_symbol;

#     ifdef DEBUG_ITP
      std::cout <<"   ~~~~ smth more: "<< it2->l.var_no() << " ";
#     endif
    }
#   ifdef DEBUG_ITP
    std::cout << std::endl;
#   endif
  }

# ifdef DEBUG_ITP
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
# endif

  // Do the renaming itself
  bool used_symbols[symbols.size()];
  memset(&used_symbols, 0, sizeof(used_symbols));
  
  unsigned shift = _no_orig_variables - cannon_var_no;
  for (clausest::iterator it = clauses.begin();
          it != clauses.end();
          ++it) {
    for (bvt::iterator it2 = it->begin();
            it2 != it->end();
            ++it2) {

      // Only shift the artificial variables (present due to the Tseitin
      // encoding to CNF)
      if (it2->var_no() > max_var) {
        if (shift > it2->var_no()){
          std::cout << "Failed to generalize interpolant\n";
          // possibly, due to pointers
          root_literal = const_literal(true);
          return;
        }
        it2->set(it2->var_no() - shift, it2->sign());
        continue;
      } 

      int idx = it2->var_no() - min_var;
      // Sanity check, all variables used in the interpolant should be mapped.
      assert (idx >= 0);
      assert(renaming[idx] != UINT_MAX);
      it2->set(renaming[idx], it2->sign());
      used_symbols[represented_symbol[idx]] = true;
    }
  }
  if (root_literal.var_no() > max_var) {
    root_literal.set(root_literal.var_no() - shift, root_literal.sign());
  } else {
    unsigned idx = root_literal.var_no() - min_var;
    // Sanity check, all variables used in the interpolant should be mapped.
    assert(renaming[idx] != UINT_MAX);
    root_literal.set(renaming[idx], root_literal.sign());
    used_symbols[represented_symbol[idx]] = true;
  }

  free(renaming);
  free(represented_symbol);

  // TODO: This line was broken - substitution could not guess variables, if some were not used 
  // _no_variables -= shift;
  
# ifdef DEBUG_ITP
  std::cout << "_cannon_vars: " << cannon_var_no << std::endl;
  std::cout << "_no_vars: " << _no_variables << std::endl;
  std::cout << "_no_orig_vars: " << _no_orig_variables << std::endl;
# endif
  _no_variables = cannon_var_no + (_no_variables - _no_orig_variables);
  _no_orig_variables = cannon_var_no;
  
  symbol_mask.reserve(symbols.size());
  for (unsigned i = 0; i < symbols.size(); ++i) {
    symbol_mask.push_back(used_symbols[i]);
  }

  // TODO: Should we force mapping of common symbols to fresh prop. variables
  // in order to prevent unification?

# ifdef DEBUG_ITP
  std::cout << "After generalization: " << std::endl;
  print(std::cout);
# endif
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
  vec<PTRef>& args = tterm->getArgs();
  Map<PTRef, PtAsgn, PTRefHash> subst;
  for(int i = 0; i < symbols.size(); ++i)
  {
      string fixed_str = id2string(symbols[i].get_identifier());
      fixed_str = smtcheck_opensmt2t::remove_index(fixed_str);
      fixed_str = smtcheck_opensmt2t::quote_varname(fixed_str);
      for(int j = 0; j < args.size(); ++j)
      {
          string aname = string(logic->getSymName(args[j]));
          aname = smtcheck_opensmt2t::quote_varname(aname);
          if(aname == fixed_str)
          {
              literalt l = decider.convert(symbols[i]);
              PTRef tmp = decider.literal2ptref(l);
              subst.insert(args[j], PtAsgn(tmp, l_True));
          }
      }
  }
  PTRef part_sum;
  PTRef templ = tterm->getBody();
  logic->varsubstitute(templ, subst, part_sum);
  decider.set_to_true(part_sum);
  cout << "; Template instantiated is " << logic->printTerm(part_sum) << endl;
    


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

void smt_itpt::reserve_variables(prop_convt& decider,
    const std::vector<symbol_exprt>& symbols, std::map<symbol_exprt, std::vector<unsigned> >& symbol_vars)
{
  // FIXME: Dirty cast.
  boolbv_mapt& map = const_cast<boolbv_mapt&>(dynamic_cast<boolbvt&>(decider).get_map());

  // Force existence of the variables
  for (std::vector<symbol_exprt>::const_iterator it = symbols.begin();
          it != symbols.end();
          ++it) {
    std::vector<unsigned> new_lit;

    // Bool symbols are not in the boolbv_map and have to be treated separately
    if (it->type().id() == ID_bool) {
      literalt l = decider.convert(*it);
      new_lit.push_back(l.var_no());
      continue;
    }
    boolbv_mapt::map_entryt& m_entry = 
            map.get_map_entry(it->get_identifier(), it->type());
    for (unsigned i = 0;
            i < m_entry.width;
            ++i) {
      // Copied from boolbv_map to speedup the query
      assert(i < m_entry.literal_map.size());
      if(!m_entry.literal_map[i].is_set) {
        m_entry.literal_map[i].is_set = true;
        m_entry.literal_map[i].l = decider.prop.new_variable();
      }
      new_lit.push_back(m_entry.literal_map[i].l.var_no());
    }
    symbol_vars[*it] = new_lit;
  }
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
    out << "Prop. interpolant (#v: " << _no_variables << ", #c: " << no_clauses() <<
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

Function: smt_itpt::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt_itpt::print_clause(std::ostream& out, const bvt& clause) const {
  for (bvt::const_iterator it2 = clause.begin();
          it2 != clause.end(); ++it2) {
    if (it2 != clause.begin())
      out << " ";
    out << it2->dimacs();
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
    logic->dumpFunction(out, tterm);
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
