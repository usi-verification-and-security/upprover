/*******************************************************************\

Module: Wrapper for OpenSMT2. Based on smtcheck_opensmt2s.

Author: Grigory Fedyukovich

\*******************************************************************/
#include <queue>

#include "smtcheck_opensmt2.h"

//#define SMT_DEBUG
//#define DEBUG_SSA_SMT
//#define DEBUG_SSA_SMT_NUMERIC_CONV
//#define DEBUG_SMT_ITP
//#define DEBUG_SMT2SOLVER

const string smtcheck_opensmt2t::_unsupported_var_str = "hifrog::c::unsupported_op2var!0#";
unsigned smtcheck_opensmt2t::unsupported2var = 0;

// Free all resources related to OpenSMT2
void smtcheck_opensmt2t::freeSolver()
{
    if (osmt != NULL) delete osmt;
}

// Free all inner objects
smtcheck_opensmt2t::~smtcheck_opensmt2t()
{
    freeSolver();
    // Shall/When need to: freeSolver() ?
}

/*******************************************************************\

Function: smtcheck_opensmt2t::new_partition

  Inputs:

 Outputs: returns a unique partition id

 Purpose: Begins a partition of formula for latter reference during
 interpolation extraction. All assertions made until
 next call of new_partition() will be part of this partition.

\*******************************************************************/
fle_part_idt smtcheck_opensmt2t::new_partition()
{

  // Finish the previous partition if any
  if (current_partition != NULL)
    close_partition();

  current_partition = new vec<PTRef>();

  return partition_count++;
}

literalt smtcheck_opensmt2t::new_variable()
{
  literalt l;
  l.set(no_literals, false);
  no_literals++;
  return l;
}

/*******************************************************************\

Function: smtcheck_opensmt2t::push_variable

  Inputs: PTRef to store

 Outputs: Literal that has the index of the stored PTRef in literals

 Purpose: To check if the store of PTRef in literals is sound
 That is given a literal we will always get the original PTRef
 (or error index) - but no other PTRefs...

 NOTE: IN CASE YOU HAVE AN ASSERTION VIOLATION FROM THIS CODE
 	 	 D O   N O T   C O M M E N T   THE DEBUG PRINTS
 	 	 IT SAYS THAT THE MAPPING OF LITERALS TO PTREFS
 	 	 ARE NOT WORKING!! FIX IT, PLEASE
 	 	 REASON: PTREF IS A STRUCT AND VECTOR AND STRUCTS
 	 	 HAVE SOME ISSUES...

\*******************************************************************/
literalt smtcheck_opensmt2t::push_variable(PTRef ptl) {
	literalt l = new_variable();
#ifdef SMT_DEBUG
	// If this assert fails try to check location 0,1 and the rest of the data in literals
	assert(l.var_no() == literals.size());
#endif
	literals.push_back(ptl); // Keeps the new literal + index it
#ifdef SMT_DEBUG
	// THE MAPPING IS WRONG. YOU ARE NOT GETTING THE CORRECT PTREF!!
	assert(ptl.x == (literals[l.var_no()]).x);
#endif
	return l; // Return the literal after creating all ok - check if here with SMT_DEBUG flag
}

// TODO: enhance this to get assignments for any PTRefs, not only for Bool Vars.
bool smtcheck_opensmt2t::is_assignemt_true(literalt a) const
{
  if (a.is_true())
    return true;
  else if (a.is_false())
    return false;

  ValPair a_p = mainSolver->getValue(literals[a.var_no()]);
  return ((*a_p.val == *true_str) ^ (a.sign()));
}

// For using symbol only when creating the interpolant (in smt_itpt::substitute)
PTRef smtcheck_opensmt2t::convert_symbol(const exprt &expr)
{
    // Assert if not symbol_exprt
    assert(expr.id()==ID_symbol || expr.id()==ID_nondet_symbol);

    // If it is a symbol create the PTRef for it and returns it
    literalt l = convert(expr);
    return literals[l.var_no()];
}

literalt smtcheck_opensmt2t::const_var(bool val)
{
    PTRef c = val ? logic->getTerm_true() : logic->getTerm_false();
    return push_variable(c); // Keeps the new PTRef + create for it a new index/literal
}

void smtcheck_opensmt2t::set_to_true(PTRef ptr)
{
    push_variable(ptr); // Keeps the new PTRef + create for it a new index/literal
    assert(ptr != PTRef_Undef);
    current_partition->push(ptr);
}

void smtcheck_opensmt2t::set_to_true(const exprt &expr)
{
    literalt l = convert(expr);
    PTRef lp = literals[l.var_no()];
    PTRef truep = logic->getTerm_true();
    vec<PTRef> args;
    args.push(lp);
    args.push(truep);
    PTRef tlp = logic->mkEq(args);

    assert(tlp != PTRef_Undef);
    current_partition->push(tlp);
}

void smtcheck_opensmt2t::set_to_false(const exprt &expr)
{
    literalt l = convert(expr);
    PTRef lp = literals[l.var_no()];
    PTRef falsep = logic->getTerm_false();
    vec<PTRef> args;
    args.push(lp);
    args.push(falsep);
    PTRef tlp = logic->mkEq(args);

    assert(tlp != PTRef_Undef);
    current_partition->push(tlp);
}

void smtcheck_opensmt2t::set_equal(literalt l1, literalt l2){
    vec<PTRef> args;
    PTRef pl1 = literals[l1.var_no()];
    PTRef pl2 = literals[l2.var_no()];
    args.push(pl1);
    args.push(pl2);
    PTRef ans = logic->mkEq(args);
    literalt l = push_variable(ans); // Keeps the new PTRef + create for it a new index/literal
    assert(ans != PTRef_Undef);
    current_partition->push(ans);
}

literalt smtcheck_opensmt2t::limplies(literalt l1, literalt l2){
    vec<PTRef> args;
    PTRef pl1 = literals[l1.var_no()];
    PTRef pl2 = literals[l2.var_no()];
    args.push(pl1);
    args.push(pl2);
    PTRef ans = logic->mkImpl(args);
    return push_variable(ans); // Keeps the new PTRef + create for it a new index/literal
}

literalt smtcheck_opensmt2t::land(literalt l1, literalt l2){
    vec<PTRef> args;
    PTRef pl1 = literals[l1.var_no()];
    PTRef pl2 = literals[l2.var_no()];
    args.push(pl1);
    args.push(pl2);
    PTRef ans = logic->mkAnd(args);
    return push_variable(ans); // Keeps the new PTRef + create for it a new index/literal
}

literalt smtcheck_opensmt2t::land(bvt b){
    vec<PTRef> args;
    for(bvt::iterator it = b.begin(); it != b.end(); ++it)
    {
        PTRef tmpp = literals[it->var_no()];
        args.push(tmpp);
    }
    PTRef ans = logic->mkAnd(args);
    return push_variable(ans); // Keeps the new PTRef + create for it a new index/literal
}

literalt smtcheck_opensmt2t::lor(literalt l1, literalt l2){
    vec<PTRef> args;
    PTRef pl1 = literals[l1.var_no()];
    PTRef pl2 = literals[l2.var_no()];
    args.push(pl1);
    args.push(pl2);
    PTRef ans = logic->mkOr(args);
    return push_variable(ans); // Keeps the new PTRef + create for it a new index/literal
}

literalt smtcheck_opensmt2t::lor(bvt b){
    vec<PTRef> args;
    for(bvt::iterator it = b.begin(); it != b.end(); ++it)
    {
        PTRef tmpp = literals[it->var_no()];
        args.push(tmpp);
    }
    PTRef ans = logic->mkOr(args);
    return push_variable(ans); // Keeps the new PTRef + create for it a new index/literal
}

literalt smtcheck_opensmt2t::lnot(literalt l){
    vec<PTRef> args;
    PTRef pl1 = literals[l.var_no()];
    args.push(pl1);
    PTRef ans = logic->mkNot(args);
    return push_variable(ans); // Keeps the new PTRef + create for it a new index/literal
}

literalt smtcheck_opensmt2t::lconst(const exprt &expr){
    if (expr.is_boolean()) {
        return const_var(expr.is_true());
    } else if (expr.type().id() == ID_c_bool) { // KE: New Cprover code - patching
        std::string num(expr.get_string(ID_value));
        assert(num.size() == 8); // if not 8, but longer, please add the case
        return const_var(num.compare("00000000") != 0);
        //std::cout << "Check? " << (num.compare("00000000") != 0) << " for string " << num << std::endl;
    } else {
        return const_var_Real(expr);
    }
}

#ifdef PRODUCE_PROOF
void smtcheck_opensmt2t::extract_itp(PTRef ptref, smt_itpt& itp) const
{
  // KE : interpolant adjustments/remove var indices shall come here
  itp.setInterpolant(ptref);
}

// helper interpolation method taken from opensmt
void smtcheck_opensmt2t::produceConfigMatrixInterpolants (const vector< vector<int> > &configs, vector<PTRef> &interpolants)
{
  SimpSMTSolver& solver = osmt->getSolver();

  // First interpolant is true -> all partitions in B
  for ( unsigned i = 0; i < configs.size(); i++ )
  {
    ipartitions_t mask = 0;
    for (unsigned j = 0; j < configs[i].size(); j++)
    {
      // Set partitions[i] bit to 1 (starting from bit 1, bit 0 is untouched)
      setbit ( mask, configs[i][j] + 1);
    }

    solver.getSingleInterpolant(interpolants, mask);
  }
}
#endif

string
smtcheck_opensmt2t::unquote_varname(const string& varname)
{
    int s = varname.length();
    int l = 0;
    if(varname[l] == '|') ++l;
    if(varname[s - 1] == '|')
        return string(varname.begin() + l, varname.begin() + (s - 1));
    return string(varname.begin() + l, varname.end());
}

string
smtcheck_opensmt2t::insert_index(const string& _varname, int _idx)
{
    string unidx = remove_index(_varname);
    string varname = unquote_varname(unidx);
    return quote_varname(varname + "#" + std::to_string(_idx));
}

string
smtcheck_opensmt2t::insert_index(const string& _varname, const string& _idx)
{
    string unidx = remove_index(_varname);
    string varname = unquote_varname(unidx);
    return quote_varname(varname + "#" + _idx);
}

int
smtcheck_opensmt2t::get_index(const string& _varname)
{
    string varname = unquote_varname(_varname);
    int i = 0;
    int s = varname.length();
    while(i < s && varname[i++] != '#');
    if(i >= s) return -1;
    string num = string(varname.begin() + i, varname.end());
    stringstream ss(num);
    int nnum;
    ss >> nnum;
    return nnum;
}

string
smtcheck_opensmt2t::quote_varname(const string& varname)
{
    if(is_quoted_var(varname)) return varname;

    string ans("");
    assert(varname.length() > 0);
    if(varname[0] != '|')
        ans += '|';
    ans += varname;
    if(varname[varname.length() - 1] != '|')
        ans += '|';
    return ans;
}

#ifdef PRODUCE_PROOF
void
smtcheck_opensmt2t::adjust_function(smt_itpt& itp, std::vector<symbol_exprt>& common_symbs, string _fun_name, bool substitute)
{
    //map<string, PTRef> vars;
    PTRef itp_pt = itp.getInterpolant();

    string fun_name = quote_varname(_fun_name);

    // retrieve variables
    //fill_vars(itp_pt, vars);

    // formatted names of common vars
    std::vector<string> quoted_varnames;
    std::map<string, PTRef> var2ptref;
    for (std::vector<symbol_exprt>::iterator it = common_symbs.begin(); it != common_symbs.end(); ++it)
    {
        string _var_name = id2string(it->get_identifier());
        if(is_cprover_rounding_mode_var(_var_name)) continue;
        if(_var_name.find("__CPROVER_") != string::npos) continue;
        if(_var_name.find("nil") != string::npos) continue;
        string var_name = remove_invalid(_var_name);
        var_name = quote_varname(var_name);
        quoted_varnames.push_back(var_name);
        var2ptref[var_name] = convert_symbol(*it);
    }

    // build substitution map (removing indices)
    // meanwhile, add the vars to Tterm
    Tterm *tterm = new Tterm();
    Map<PTRef,PtAsgn,PTRefHash> subst;

    map<string, int[3]> occurrences;
    // first we should account for repetitions in the non-indexed varnames
    //for(map<string, PTRef>::iterator it = vars.begin(); it != vars.end(); ++it)
    for(vector<string>::iterator it = quoted_varnames.begin(); it != quoted_varnames.end(); ++it)
    {
        string unidx = remove_index(*it);
        if(occurrences.find(unidx) == occurrences.end())
        {
            occurrences[unidx][0] = 1;
            occurrences[unidx][1] = get_index(*it);
        }
        else
        {
            ++occurrences[unidx][0];
            assert(occurrences[unidx][0] == 2);
            int new_idx = get_index(*it);
            int old_idx = occurrences[unidx][1];
            if(new_idx < old_idx) swap(new_idx, old_idx);
            occurrences[unidx][1] = old_idx;
            occurrences[unidx][2] = new_idx;
        }
    }

    // now we can compute the substitutions properly
    bool only_common_vars_in_itp = true;
#ifdef DEBUG_SMT_ITP
    cout << "; Variables in the interpolant: " << endl;
#endif
    //for(map<string, PTRef>::iterator it = vars.begin(); it != vars.end(); ++it)
    for(vector<string>::iterator it = quoted_varnames.begin(); it != quoted_varnames.end(); ++it)
    {
#ifdef DEBUG_SMT_ITP
        cout << " * " << *it << ' ';
#endif
        if (quoted_varnames.end() ==
            find (quoted_varnames.begin(), quoted_varnames.end(), *it)){
#ifdef DEBUG_SMT_ITP
            cout << " ---> local var to A; should not be in the interpolant";
#endif
            only_common_vars_in_itp = false;
        }

        string unidx = remove_index(*it);
        int occ = occurrences[unidx][0];
        assert(occ >= 1 && occ <= 2);

        string new_var_name = unidx;

        if(occ == 2)
        {
            int idx = get_index(*it);
            int l = occurrences[unidx][1];
            int r = occurrences[unidx][2];
            if(idx == l)
                new_var_name = insert_index(new_var_name, "in");
            else
            {
                assert(idx == r);
                new_var_name = insert_index(new_var_name, "out");
            }
        }

        PTRef var = PTRef_Undef;
        var = var2ptref[*it];
        assert(var != PTRef_Undef);
        assert(new_var_name.size() > 0);
        PTRef new_var = logic->mkVar(logic->getSortRef(var), new_var_name.c_str());
        tterm->addArg(new_var);
        subst.insert(var, PtAsgn(new_var, l_True));
#ifdef DEBUG_SMT_ITP
        cout << endl;
#endif
    }

    assert(only_common_vars_in_itp);

    PTRef new_root;
    // substitute
    if(substitute)
    {
        logic->varsubstitute(itp_pt, subst, new_root);
        //cout << "; Formula " << logic->printTerm(itp.getInterpolant()) << " is now " << logic->printTerm(new_root) << endl;
    }
    else
    {
        new_root = logic->getTerm_true();
    }
    tterm->setBody(new_root);

    tterm->setName(fun_name);
    //logic->addFunction(tterm);
    //logic->dumpFunction(cout, tterm);
    itp.setTterm(*tterm);
    itp.setLogic(logic);
}
#endif 

void
smtcheck_opensmt2t::fill_vars(PTRef itp, map<string, PTRef>& subst)
{
#ifdef PRODUCE_PROOF
    set<PTRef> visited;
    queue<PTRef> q;
    q.push(itp);
    while(!q.empty())
    {
        PTRef p = q.front();
        q.pop();
        if(visited.find(p) != visited.end())
            continue;
        if(logic->isVar(p))
            subst[logic->getSymName(p)] = p;
        else
        {
            Pterm& pt = logic->getPterm(p);
            for(int i = 0; i < pt.size(); ++i)
                q.push(pt[i]);
        }
        visited.insert(p);
    }
#else
    assert(0);
#endif
}

bool
smtcheck_opensmt2t::is_quoted_var(const string& varname)
{
    assert(varname.length() > 0);
    return (varname[0] == '|') && (varname[varname.length() - 1] == '|');
}

string
smtcheck_opensmt2t::remove_invalid(const string& varname)
{
    string ans("");
    for(unsigned int i = 0; i < varname.length(); ++i)
    {
        if(varname[i] != '\\')
            ans += varname[i];
    }
    return ans;
}

string
smtcheck_opensmt2t::remove_index(string var)
{
    int i = var.length() - 1;
    while(i >= 0 && var[i] != '#') --i;
    string no_index;
    if(i > 0)
        no_index = string(var.begin(), var.begin() + i);
    else
        return var;
    if(is_quoted_var(var))
        return quote_varname(no_index);
    return no_index;
}


/*******************************************************************\

Function: smtcheck_opensmt2t::get_interpolant

  Inputs:

 Outputs:

 Purpose: Extracts the symmetric interpolant of the specified set of
 partitions. This method can be called only after solving the
 the formula with an UNSAT result.

\*******************************************************************/
// KE : Shall add the code using new outputs from OpenSMT2 + apply some changes to variable indices
//      if the code is too long split to the method - extract_itp, which is now commented (its body).
#ifdef PRODUCE_PROOF 
void smtcheck_opensmt2t::get_interpolant(const interpolation_taskt& partition_ids, interpolantst& interpolants)
{   
  assert(ready_to_interpolate);
  
  const char* msg2=NULL;
  osmt->getConfig().setOption(SMTConfig::o_verbosity, verbosity, msg2);
  //if (msg2!=NULL) { free((char *)msg2); msg2=NULL; } // If there is an error consider printing the msg
  osmt->getConfig().setOption(SMTConfig::o_certify_inter, SMTOption(certify), msg2);
  //if (msg2!=NULL) free((char *)msg2); // If there is an error consider printing the msg
  
  // Set labeling functions
  osmt->getConfig().setBooleanInterpolationAlgorithm(itp_algorithm);
  osmt->getConfig().setEUFInterpolationAlgorithm(itp_euf_algorithm);
  osmt->getConfig().setLRAInterpolationAlgorithm(itp_lra_algorithm);
  if(itp_lra_factor != NULL) osmt->getConfig().setLRAStrengthFactor(itp_lra_factor);

  SimpSMTSolver& solver = osmt->getSolver();

  // Create the proof graph
  solver.createProofGraph();

  // Reduce the proof graph
  if(reduction)
  {
      osmt->getConfig().setReduction(1);
      osmt->getConfig().setReductionGraph(reduction_graph);
      osmt->getConfig().setReductionLoops(reduction_loops);
      solver.reduceProofGraph();
  }

  vector<PTRef> itp_ptrefs;

  // iterative call of getSingleInterpolant:
  produceConfigMatrixInterpolants(partition_ids, itp_ptrefs);

  solver.deleteProofGraph();

  for(unsigned i = 0; i < itp_ptrefs.size(); ++i)
  {
      smt_itpt *new_itp = new smt_itpt();
      extract_itp(itp_ptrefs[i], *new_itp);
      interpolants.push_back(new_itp);
      char *s = logic->printTerm(interpolants.back()->getInterpolant());
#ifdef DEBUG_SMT_ITP
      cout << "Interpolant " << i << " = " << s << endl;
#endif
      free(s);
  }
}

/*******************************************************************\

Function: smtcheck_opensmt2t::can_interpolate

  Inputs:

 Outputs:

 Purpose: Is the solver ready for interpolation? I.e., the solver was used to 
 decide a problem and the result was UNSAT

\*******************************************************************/
bool smtcheck_opensmt2t::can_interpolate() const
{
  return ready_to_interpolate;
}
#endif

/*******************************************************************\

Function: smtcheck_opensmt2t::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool smtcheck_opensmt2t::solve() {

  //if (dump_queries){
  //  char* msg1=NULL;
  //  mainSolver->writeSolverState_smtlib2("__SMT_query", &msg1);
  //  if (msg1 != NULL) free(msg1);
  //}

#ifdef PRODUCE_PROOF    
  ready_to_interpolate = false;
#endif
  
  if (current_partition != NULL) {
    close_partition();
  }

#ifdef DEBUG_SMT4SOLVER
  logic->dumpHeaderToFile(cout);
#endif
//  add_variables();
    char *msg=NULL;
    for(int i = pushed_formulas; i < top_level_formulas.size(); ++i) {
#ifdef DEBUG_SMT4SOLVER
        char* s = logic->printTerm(top_level_formulas[i]);
        cout << "\n(assert\n" << s << "\n)" << endl;
        free(s);
#endif
        mainSolver->insertFormula(top_level_formulas[i], &msg);
	if (msg != NULL) {
            free(msg); // If there is an error, consider print msg
	    msg=NULL;
	}
    }
    
    pushed_formulas = top_level_formulas.size();
#ifdef DEBUG_SMT4SOLVER
    dump_on_error("smtcheck_opensmt2t::solve::1082"); // To print current code in the solver
#endif

    sstat r = mainSolver->check();

    if (r == s_True) {
        return true;
    } else if (r == s_False) {
#ifdef PRODUCE_PROOF        
        ready_to_interpolate = true;
#endif
    } else {
        throw "Unexpected OpenSMT result.";
    }

    return false;
}


/*******************************************************************\

Function: smtcheck_opensmt2t::close_partition

  Inputs:

 Outputs:

 Purpose: Closes the interpolation partition by passing its CNF form
 (collected in current_partition) to the solver.

\*******************************************************************/

void smtcheck_opensmt2t::close_partition()
{
  assert(current_partition != NULL);
  if (partition_count > 0){
    if (current_partition->size() > 1){
      PTRef pand = logic->mkAnd(*current_partition);
#ifdef DEBUG_SMT2SOLVER
      char* s= logic->printTerm(pand);
      cout << "; Pushing to solver: " << s << endl;
      free(s);
#endif
      top_level_formulas.push(pand);
    } else if (current_partition->size() == 1){
      PTRef pand = (*current_partition)[0];
#ifdef DEBUG_SMT2SOLVER
      cout << "Trivial partition (terms size = 1): " << partition_count << "\n";
      char* s= logic->printTerm(pand);
      cout << "; Pushing to solver: " << s << endl;
      free(s);
#endif
      top_level_formulas.push(pand);
    } /*else {
      // GF: adding (assert true) for debugging only
      top_level_formulas.push(logic->getTerm_true());
    } */
  }

  current_partition = NULL;
}

/*******************************************************************\

Function: smtcheck_opensmt2t::getVars

  Inputs: -

 Outputs: a set of all variables that used in the smt formula

 Purpose: get all the vars to create later on the counter example path

\*******************************************************************/
std::set<PTRef>* smtcheck_opensmt2t::getVars()
{
    std::set<PTRef>* ret = new std::set<PTRef>();
    for(it_literals it = literals.begin(); it != literals.end(); it++)
    {
        if ((logic->isVar(*it)) && (ret->count(*it) < 1))
            ret->insert(*it);
    }

    return ret;
}

/*******************************************************************\

Function: smtcheck_opensmt2t::extract_expr_str_number

  Inputs: expression that is a constant (+/-/int/float/rational)

 Outputs: a string of the number

 Purpose: assure we are extracting the number correctly.

 expr.get(ID_C_cformat).c_str() - doesn't work for negative numbers!
 * And thanks god (the starts and mother nature) that this option 
 * is NOT in new Cprover framework

\*******************************************************************/
std::string smtcheck_opensmt2t::extract_expr_str_number(const exprt &expr)
{
    std::string const_val = expr.print_number_2smt(); // DO NOT CHANGE TO cprover util code as it works only for positive or unsigned!
    //(unless upgrade, please keep the checks/assert!)
    // If can be that we missed more cases... use the debug prints to check conversions!!
#ifdef DEBUG_SSA_SMT_NUMERIC_CONV
    cout << "; EXTRACTING NUMBER " << const_val 
            << " (ORIG-EXPR " << expr.get(ID_value) 
            << " :: " << expr.type().id() << ")" << endl;
    //cout << "; TEST FOR EXP C FORMAT GIVES " << expr.get(ID_C_cformat).c_str() << " with TYPE " << expr.type().id_string() << endl;
#endif

    return const_val;
}

/*******************************************************************\

Function: smtcheck_opensmt2t::extract_expr_str_name

  Inputs: expression that is a var

 Outputs: a string of the name

 Purpose: assure we are extracting the name correctly and in one place.

\*******************************************************************/
std::string smtcheck_opensmt2t::extract_expr_str_name(const exprt &expr)
{
    string str = id2string(expr.get(ID_identifier));
    assert (str.size() != 0); // Check the we really got something

    if(expr.id() == ID_nondet_symbol && str.find("nondet") == std::string::npos)
            str = str.replace(0,7, "symex::nondet");

    if (is_cprover_rounding_mode_var(str)) 
    {
    #ifdef DEBUG_SSA_SMT // KE - Remove assert if you wish to have debug info
        cout << "; " << str << " :: " << expr.id() << " - Should Not Add Rounding Model\n" << expr.pretty() << endl;
    #else
        cout << "EXIT WITH ERROR: Using Rounding Model not in propositional logic" << str << endl;
        assert(false);
    #endif
    }

    if (str.find("__CPROVER_") != std::string::npos) {
    #ifdef DEBUG_SSA_SMT // KE - Remove assert if you wish to have debug info
        cout << "; " << str << " :: " << expr.id() << " - Should Not Add Cprover Built-ins\n" << expr.pretty() << endl;
    #else
        cout << "EXIT WITH ERROR: Using CPROVER built-in variables not in propositional logic " << str << endl;
        //assert(false); //KE: when found all reasons - uncomment
    #endif
    }

    return str;
}

/*******************************************************************\

Function: smtcheck_opensmt2t::dump_on_error

  Inputs: location where the error happened

 Outputs: cout the current smt encoding (what did so far) to the cout

 Purpose: To know what is the problem while encoding the formula

\*******************************************************************/
void smtcheck_opensmt2t::dump_on_error(std::string location) 
{
    //If have problem with declaration of vars - uncommen this!
#ifdef DEBUG_SMT4SOLVER
    cout << "; XXX SMT-lib --> Current Logic Translation XXX" << endl;
    cout << "; Declarations from two source: if there is no diff use only one for testing the output" << endl;
    cout << "; Declarations from Hifrog :" << endl;
    for(it_var_set_str iterator = var_set_str.begin(); iterator != var_set_str.end(); iterator++) {
            cout << "(declare-fun " << *iterator << ")" << endl;
    }
    cout << "; Declarations from OpenSMT2 :" << endl;
#endif
    logic->dumpHeaderToFile(cout);
    cout << "(assert\n  (and" << endl;
    for(int i = 0; i < top_level_formulas.size(); ++i) {
        PTRef tmp;
        logic->conjoinExtras(top_level_formulas[i], tmp);
        char *s = logic->printTerm(tmp);
        cout << "; XXX Partition: " << i << endl << "    " << s << endl;
        free(s);
    }

    // If code - once needed uncomment this debug flag in the header
#ifdef DEBUG_SMT4SOLVER
    int size_oite = ite_map_str.size()-1; // since goes from 0-(n-1) 
    int i = 0;
    for(it_ite_map_str iterator = ite_map_str.begin(); iterator != ite_map_str.end(); iterator++) {
        cout << "; XXX oite symbol: (" << i << " out of " << size_oite << ")" 
                << iterator->first << endl << iterator->second << endl;
        i++;
    }
#endif
    cout << "))" << endl << "(check-sat)" << endl;
}

std::string smtcheck_opensmt2t::create_bound_string(std::string base, int exp)
{
    std::string ret = base;
    int size = exp - base.size() + 1; // for format 3.444444
    for (int i=0; i<size;i++)
        ret+= "0";

    return ret;
}