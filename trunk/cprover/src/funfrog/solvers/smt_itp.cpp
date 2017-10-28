#include "smtcheck_opensmt2.h"
#include "../hifrog.h"
#include "smt_itp.h"

//#define DEBUG_ITP_SMT
# ifdef DEBUG_ITP_SMT
#include <iostream>
#endif

bool
smt_itpt::usesVar(symbol_exprt& symb, unsigned idx)
{
    assert(tterm != NULL && logic != NULL);
    string var_name = smtcheck_opensmt2t::remove_invalid(get_symbol_name(symb).c_str());
    const vec<PTRef>& args = tterm->getArgs();
    for(int i = 0; i < args.size(); ++i)
    {
        string pname = logic->getSymName(args[i]);
        //pname = smtcheck_opensmt2t::remove_index(pname);
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

# ifdef DEBUG_ITP_SMT
  std::cout << "--------------- Generalizing -------------" << std::endl;
# endif

 // TODO: Re-write the code for SMT (see the Prop version)
}


namespace{
    inline bool isInputGlobalName(const std::string& name){
        return name.find(HifrogStringConstants::GLOBAL_INPUT_SUFFIX) != std::string::npos;
    }

    inline bool isOutputGlobalName(const std::string& name){
        return name.find(HifrogStringConstants::GLOBAL_OUT_SUFFIX) != std::string::npos;
    }

    bool isGlobalName(const std::string& name){
        return isInputGlobalName(name) || isOutputGlobalName(name);
    }

    std::string stripGlobalSuffix(const std::string& name){
        if(isInputGlobalName(name)){
            return name.substr(0, name.length() - HifrogStringConstants::GLOBAL_INPUT_SUFFIX.length());
        }
        else if(isOutputGlobalName(name)){
            return name.substr(0, name.length() - HifrogStringConstants::GLOBAL_OUT_SUFFIX.length());
        }
        assert(false);
        return name;
    }
}

/*******************************************************************\

Function: smt_itpt::substitute

  Inputs:

 Outputs:

 Purpose: Renames propositional variables so that the interpolant is
 valid for the given set of identifiers. Moreover, the interpolant is
 asserted in the given propositional solver.
 * 
 * KE: can still be buggy as there are still manual extrations of ids
 * 
 * Originally: tryied to edit L2 ids to be original symbols to match
 * SSA expressions to summaries symbols
 * 
 * KE: not sure the code for #in #out #invs is correct

\*******************************************************************/

void smt_itpt::substitute(smtcheck_opensmt2t& decider,
    const std::vector<symbol_exprt>& symbols,
    bool inverted) const
{
    //TODO remove the inverted parameter?
    assert(!is_trivial());
    assert(tterm && logic);
    const vec<PTRef>& args = tterm->getArgs();

    // summary is defined as a function over arguments to Bool
    // we need to match the arguments with the symbols and substitute
    // the assumption is that arguments' names correspond to the base names of the symbols
    // and they are in the same order
    // one exception is if global variable is both on input and output, then the out argument was distinguished

    Map<PTRef, PtAsgn, PTRefHash> subst;
    for(std::size_t i = 0; i < symbols.size(); ++i){
        std::string symbol_name { get_symbol_name(symbols[i]).c_str() };
        PTRef argument = args[i];
        std::string argument_name { logic->getSymName(argument) };
        if(isGlobalName(argument_name)){
            argument_name = stripGlobalSuffix(argument_name);
        }
        if(symbol_name != argument_name){
            std::stringstream ss;
            ss << "Argument name read from summary do not match expected symbol name!\n"
               << "Expected symbol name: " << symbol_name << "\nName read from summary: " << argument_name;

            throw std::logic_error(ss.str());
        }
        PTRef symbol_ptref = decider.convert_symbol(symbols[i]);
        subst.insert(argument, PtAsgn(symbol_ptref, l_True));
    }

    // do the actual substiotuition
    PTRef old_root = tterm->getBody();
    PTRef new_root;
    logic->varsubstitute(old_root, subst, new_root);
    decider.set_to_true(new_root);

    // TODO: set the new root as new body?
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
            << logic->printTerm(interpolant) << std::endl;
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

/*******************************************************************\

Function: smt_itpt::is_system_translation_var

  Inputs:

 Outputs:

 Purpose: Check if a var is L1 but looks like L2 because of naming inner 
 * convention of Cprover or OpenSMT

\*******************************************************************/
bool smt_itpt::is_system_translation_var(std::string name, bool is_smt_only) const {
    if (name.find(OPENSMT_IN) != string::npos) return true;
    if (name.find(OPENSMT_OUT) != string::npos) return true;
    if (name.find(OPENSMT_INVS) != string::npos) return true;

    if (is_smt_only) 
        return false;
    else 
        return (name.find(FUNC_RETURN) != string::npos);
}


