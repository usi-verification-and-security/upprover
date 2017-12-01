/*******************************************************************\

Module: Wrapper for OpenSMT2. Based on smtcheck_opensmt2s.

Author: Grigory Fedyukovich

\*******************************************************************/
#include <queue>
#include <unordered_set>

#include "smtcheck_opensmt2.h"
#include "../hifrog.h"
#include "smt_itp.h"
#include "../utils/naming_helpers.h"

// Debug flags of this class:
//#define SMT_DEBUG
//#define DEBUG_SSA_SMT
//#define DEBUG_SSA_SMT_NUMERIC_CONV
//#define DEBUG_SMT_ITP
//#define DEBUG_SMT2SOLVER

#ifdef DISABLE_OPTIMIZATIONS
#include <fstream>
using namespace std;

#include <iostream>
#endif

unsigned smtcheck_opensmt2t::unsupported2var = 0; // Count how many instance of unsupported we have for all deciders

// Free all resources related to OpenSMT2
void smtcheck_opensmt2t::freeSolver()
{
    if (osmt != NULL) delete osmt;
}

// Free all inner objects
smtcheck_opensmt2t::~smtcheck_opensmt2t()
{
    freeSolver();
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

void smtcheck_opensmt2t::set_to_true(literalt refined_l)
{
    literalt l = refined_l;
    PTRef lp = literals[l.var_no()];
    set_to_true(lp);
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


// FIXME: move to smt_itpt class
void
smtcheck_opensmt2t::fill_vars(PTRef itp, map<string, PTRef>& subst)
{
#ifdef PRODUCE_PROOF
    set<PTRef> visited;
    std::queue<PTRef> q;
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


/*******************************************************************\

Function: smtcheck_opensmt2t::get_interpolant

  Inputs:

 Outputs:

 Purpose: Extracts the symmetric interpolant of the specified set of
 partitions. This method can be called only after solving the
 the formula with an UNSAT result.

 * KE : Shall add the code using new outputs from OpenSMT2 + apply some changes to variable indices
 *      if the code is too long split to the method - extract_itp, which is now commented (its body).
\*******************************************************************/
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

Function: smtcheck_opensmt2t::solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool smtcheck_opensmt2t::solve() {

#ifdef PRODUCE_PROOF    
  ready_to_interpolate = false;
#endif
  
  if (current_partition != NULL) {
    close_partition();
  }

#ifdef DISABLE_OPTIMIZATIONS
  ofstream out_smt;
  if (dump_pre_queries) {
    out_smt.open(pre_queries_file_name+"_"+std::to_string(get_dump_current_index())+".smt2");  
    logic->dumpHeaderToFile(out_smt);
    
    // Print the .oites terms
    int size_oite = ite_map_str.size()-1; // since goes from 0-(n-1) 
    int i = 0;
    for(it_ite_map_str iterator = ite_map_str.begin(); iterator != ite_map_str.end(); iterator++) {
        out_smt << "; XXX oite symbol: (" << i << " out of " << size_oite << ") " 
                << iterator->first << endl << "(assert "<< iterator->second << "\n)" << endl;
        i++;
    }
  }
#endif
//  add_variables();
    char *msg=NULL;
    for(int i = pushed_formulas; i < top_level_formulas.size(); ++i) {
#ifdef DISABLE_OPTIMIZATIONS
        if (dump_pre_queries)
        {
            out_smt << "; XXX Partition: " << (top_level_formulas.size() - i - 1) << endl;
            char* s = logic->printTerm(top_level_formulas[i]);
            out_smt << "(assert (and \n" << s << "\n))" << endl;
            free(s);
        }
#endif
        mainSolver->insertFormula(top_level_formulas[i], &msg);
	if (msg != NULL) {
            free(msg); // If there is an error, consider print msg
	    msg=NULL;
	}
    }
 
#ifdef DISABLE_OPTIMIZATIONS   
    if (dump_pre_queries) {
        out_smt << "(check-sat)\n" << endl;
        out_smt.close();
    }
#endif    
//#ifdef DISABLE_OPTIMIZATIONS // Use if there are issues with the variables
//    dump_on_error("smtcheck_opensmt2t::solve::1082"); // To print current code in the solver
//#endif

    pushed_formulas = top_level_formulas.size();
    sstat r = mainSolver->check();

    if (r == s_True) {
        return true;
    } else if (r == s_False && has_unsupported_info()) {
        // skip 
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
    string str = fix_symex_nondet_name(expr);
    str.erase(std::remove(str.begin(),str.end(),'\\'),str.end());
    if (is_cprover_rounding_mode_var(str)) 
    {
    #ifdef DEBUG_SSA_SMT // KE - Remove assert if you wish to have debug info
        cout << "; " << str << " :: " << expr.id() << " - Should Not Add Rounding Model\n" << expr.pretty() << endl;
    #else
        cout << "EXIT WITH ERROR: Using Rounding Model not in propositional logic " << str << endl;
        assert(false);
    #endif
    }

    if (is_cprover_builtins_var(str)) {
    #ifdef DEBUG_SSA_SMT // KE - Remove assert if you wish to have debug info
        cout << "; " << str << " :: " << expr.id() << " - Should Not Add Cprover Built-ins\n" << expr.pretty() << endl;
    #else
        cout << "EXIT WITH ERROR: Using CPROVER built-in variables not in propositional logic " << str << endl;
        //assert(false); //KE: when found all reasons - uncomment
    #endif
    }
  
    bool is_L2_symbol = is_L2_SSA_symbol(expr);
    bool is_nil_or_symex = (str.compare(NIL) == 0) || (str.find(CProverStringConstants::IO_CONST) != std::string::npos);
    if (!is_L2_symbol && !is_nil_or_symex) 
    {
        if (str.find(HifrogStringConstants::COUNTER_SEP) != std::string::npos)
            is_L2_symbol = true; // we are taking care of it somehow, e.g., static arrays
        else 
        {
            // Error message before assert!
            std::cerr << "\nWARNING: Using Symbol or L1 name instead of the L2 name in the SSA tree(" << str << ")\n" ;
            return create_new_unsupported_var(expr.type().id().c_str());
        }
    }

    // KE: assure the encoding is not using the variables name as is (why there is nil here?)
    assert("Error: using non-SSA symbol in the SMT encoding" 
            && (is_L2_symbol || is_nil_or_symex));
    // KE: we need to test how the rest of the symex vars are
    
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
#ifdef DISABLE_OPTIMIZATIONS
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
#ifdef DISABLE_OPTIMIZATIONS
    int size_oite = ite_map_str.size()-1; // since goes from 0-(n-1) 
    int i = 0;
    for(it_ite_map_str iterator = ite_map_str.begin(); iterator != ite_map_str.end(); iterator++) {
        cout << "; XXX oite symbol: (" << i << " out of " << size_oite << ") " 
                << iterator->first << endl << iterator->second << endl;
        i++;
    }
#endif
    cout << "))" << endl << "(check-sat)" << endl;
}

/*******************************************************************\

Function: smtcheck_opensmt2t::create_bound_string

 Inputs: 

 Outputs: 

 Purpose: for type constraints of CUF and LRA

\*******************************************************************/
std::string smtcheck_opensmt2t::create_bound_string(std::string base, int exp)
{
    std::string ret = base;
    int size = exp - base.size() + 1; // for format 3.444444
    for (int i=0; i<size;i++)
        ret+= "0";

    return ret;
}

/*******************************************************************\

Function: smtcheck_opensmt2t::create_new_unsupported_var

 Inputs: 

 Outputs: New unsupported global SSA name

 Purpose:

 FIXME: shall fabricate propperly the name as SSA expression
 fabricate with l2, and return the name with l2

\*******************************************************************/
string smtcheck_opensmt2t::create_new_unsupported_var(std::string type_name, bool no_rename)
{
    // Create a new unsupported va
    std::string str = UNSUPPORTED_VAR_NAME + type_name;
    if (!no_rename)
    {
    	// FIXME: SSA fabrication + rename
    	std::string prefix = "!0#" + std::to_string(unsupported2var++);
    	str += prefix;
    }

    str = quote_varname(str);
    
    assert(str.size() > 0);
    
#ifdef SMT_DEBUG
        cout << "; IT IS AN UNSUPPORTED VAR " << str << endl;
#endif
        
    return str;
}

/*******************************************************************\

Function: smtcheck_opensmt2t::store_new_unsupported_var

 Inputs: 

 Outputs: 

 Purpose: Keep which expressions are not supported and abstracted from 
 * the smt encoding

\*******************************************************************/
literalt smtcheck_opensmt2t::store_new_unsupported_var(const exprt& expr, const PTRef var, bool push_var) {        
    // If need to register the abstracted functions - add it here
    const irep_idt &_id=expr.id(); // KE: gets the id once for performance
    if ((store_unsupported_info) && (_id!=ID_symbol && _id!=ID_nondet_symbol && _id!=ID_constant))
    {
        // Map the expression to its unsupported abstracted vat (in opensmt)
        unsupported_info_map.insert(pair<PTRef, exprt> (var, expr));
        cout << "**** Saved function as a candidate for lattice refinement. ";
        char *s = logic->printTerm(var);
        cout << "Expression " << s << " will be refine the operator " 
              << _id << " with " << expr.operands().size() << " operands." 
              << endl;
        free(s);
    }
    
    if (push_var)
        return push_variable(var);
    else 
        return const_literal(true);
}

/*******************************************************************\

Function: smtcheck_opensmt2t::bind_var2refined_var

 Inputs: two ptref, one is a refined version of the other

 Outputs: (= refined coarse)

 Purpose: to connect the rest of the translation to the most refined version 
 * of expression. 
 * 
 * TODO: add pop incase we need to refine more than once!

\*******************************************************************/
literalt smtcheck_opensmt2t::bind_var2refined_var(PTRef ptref_coarse, PTRef ptref_refined) {
    // Pop the old version 
    // TODO logic->pop(ptref_coarse); // KE: or something like this or push prev ret of it

    // Create the new refined version
    PTRef ret = logic->mkEq(ptref_coarse, ptref_refined);
    
    // Keep the new ptref and return the new one
    return push_variable(ret);
}

/*******************************************************************\

Function: smtcheck_opensmt2t::get_smt_func_decl

 Inputs: name of the function and its signature

 Outputs: the function declarations

 Purpose: to create new custom function to smt from summaries

\*******************************************************************/
SymRef smtcheck_opensmt2t::get_smt_func_decl(const char* op, SRef& in_dt, vec<SRef>& out_dt) {
    char *msg=NULL;
    SymRef ret = logic->declareFun(op, in_dt, out_dt, &msg, true);
    if (msg != NULL) free(msg);

    return ret;    
}

/*******************************************************************\

Function: smtcheck_opensmt2t::create_equation_for_unsupported

  Inputs:

 Outputs:

 Purpose:

 *  If not exist yet, creates a new declartion in OpenSMT with 
 *  function name+size of args+type. 
 *  Add a new ptref of the use for this expression
\*******************************************************************/
PTRef smtcheck_opensmt2t::create_equation_for_unsupported(const exprt &expr)
{  
    // extract parameters to the call
    vec<PTRef> args; 
    get_unsupported_op_args(expr, args);
    
    // Define the function if needed and check it is OK
    SymRef decl = get_unsupported_op_func(expr, args);
    
#ifdef SMT_DEBUG    
    std::cout << ";;; Use Unsupported function: " << logic->printSym(decl) << std::endl;
#endif    
    
    return mkFun(decl, args);
}

/*******************************************************************\

Function: smtcheck_opensmt2t::get_unsupported_op_func

  Inputs:

 Outputs: the usupported operator symbol to be used later in
 * mkFun method

 Purpose:
 *  If not exist yet, creates a new declartion in OpenSMT with 
 *  function name+size of args+type. 
\*******************************************************************/
SymRef smtcheck_opensmt2t::get_unsupported_op_func(const exprt &expr, const vec<PTRef>& args)
{
    const irep_idt &_func_id=expr.id(); // Which function we will add as uninterpurted
    std::string func_id(_func_id.c_str());
    func_id = "uns_" + func_id;
    
    // First declare the function, if not exist
    std::string key_func(func_id.c_str());
    key_func += "," + getStringSMTlibDatatype(expr);
    SRef out = getSMTlibDatatype(expr);

    vec<SRef> args_decl;
    for (int i=0; i < args.size(); i++) 
    {
        args_decl.push(logic->getSortRef(args[i]));
        key_func += "," + std::string(logic->getSortName(logic->getSortRef(args[i])));
    }
     
    // Define the function if needed and check it is OK
    SymRef decl = SymRef_Undef;
    if (decl_uninterperted_func.count(key_func) == 0) {
        decl = get_smt_func_decl(func_id.c_str(), out, args_decl);
        decl_uninterperted_func.insert(pair<string, SymRef> (key_func,decl));
    } else {
        decl = decl_uninterperted_func.at(key_func);
    }
    assert(decl != SymRef_Undef);
    
    return decl;
}

/*******************************************************************\

Function: smtcheck_opensmt2t::get_unsupported_op_args

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void smtcheck_opensmt2t::get_unsupported_op_args(const exprt &expr, vec<PTRef> &args)
{
    // The we create the new call
    forall_operands(it, expr)
    {	
        if (is_cprover_rounding_mode_var(*it)) continue;
        // Skip - we don't need the rounding variable for non-bv logics + assure it is always rounding thing

        PTRef cp = literals[convert(*it).var_no()];
        assert(cp != PTRef_Undef);
        args.push(cp); // Add to call
    }
}

/*******************************************************************\

Function: smtcheck_opensmt2t::mkFun

  Inputs: function signature in SMTlib with arguments

 Outputs: PTRef of it (with the concrete args)

 Purpose: General mechanism to call uninturpruted functions
          Mainly for a new custom function to smt from summaries

\*******************************************************************/
PTRef smtcheck_opensmt2t::mkFun(SymRef decl, const vec<PTRef>& args)
{
    char *msg=NULL;
    PTRef ret = logic->mkFun(decl, args, &msg);
    if (msg != NULL) free(msg);  
    
    return ret;
}

/*******************************************************************\

Function: smtcheck_opensmt2t::getStringSMTlibDatatype

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
std::string smtcheck_opensmt2t::getStringSMTlibDatatype(const exprt& expr)
{
    typet var_type = expr.type(); // Get the current type
    if ((var_type.id()==ID_bool) || (var_type.id() == ID_c_bool) || (is_number(var_type)))
        return getStringSMTlibDatatype(var_type);
    else {
        literalt l_unsupported = lunsupported2var(expr);
        PTRef var = literals[l_unsupported.var_no()];
        
        return std::string(logic->getSortName(logic->getSortRef(var)));
    }
}

/*******************************************************************\

Function: smtcheck_opensmt2t::getSMTlibDatatype

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
SRef smtcheck_opensmt2t::getSMTlibDatatype(const exprt& expr)
{
    typet var_type = expr.type(); // Get the current type
    if ((var_type.id()==ID_bool) || (var_type.id() == ID_c_bool) || (is_number(var_type)))
        return getSMTlibDatatype(var_type);
    else {
        literalt l_unsupported = lunsupported2var(expr);
        PTRef var = literals[l_unsupported.var_no()];
        
        return logic->getSortRef(var);
    }
}

// FIXME: move to hifrog or util in hifrog
#ifdef PRODUCE_PROOF
namespace {
    bool is_global(const exprt& expr){
        if(!expr.get_bool(ID_C_SSA_symbol)){
            return false;
        }
        return to_ssa_expr(expr).get_level_0().empty();
    }
}

// FIXME: move to smt_itpt class
void smtcheck_opensmt2t::generalize_summary(smt_itpt &interpolant, std::vector<symbol_exprt> &common_symbols,
                                            const std::string &fun_name, bool substitute)
{
    // Right now the term is not set, hence the assert, but this should actually be set somewhere else
    assert(interpolant.getTterm() == nullptr);
    if(is_cprover_initialize_method(fun_name)){
        throw std::logic_error("Summary generalize should not be called for CPROVER initialize method!");
    }
    // initialization of new Tterm, TODO: the basic should really be set already when interpolant object is created
    Tterm* tt = new Tterm();
    tt->setName(fun_name.c_str());
    interpolant.setLogic(logic);
    interpolant.setTterm(*tt);

    // prepare the substituition map how OpenSMT expects it
    Map<PTRef,PtAsgn,PTRefHash> subst;
    std::unordered_set<std::string> globals;
    for(const auto& expr : common_symbols){
        // get the original PTRef for this expression
        PTRef original = convert_symbol(expr);
        // get the new name for the symbol;
        std::string symbol_name { get_symbol_name(expr).c_str() };
        if(is_global(expr)){
            if(globals.find(symbol_name) != globals.end()){
                // global symbol encountered second time -> must be in/out pair, add suffix to this out
                symbol_name = symbol_name + HifrogStringConstants::GLOBAL_OUT_SUFFIX;
            }
            else{
                globals.insert(symbol_name);
                symbol_name = symbol_name + HifrogStringConstants::GLOBAL_INPUT_SUFFIX;
            }
        }
        // get new PTRef for the variable with new name
        PTRef new_var = logic->mkVar(logic->getSortRef(original), symbol_name.c_str());
//        std::cout << "; Original variable: " << logic->printTerm(original) << '\n';
//        std::cout << "; New variable: " << logic->printTerm(new_var) << '\n';
        subst.insert(original, PtAsgn{ new_var, l_True });
        tt->addArg(new_var);
    }
    //apply substituition to the interpolant
    PTRef old_root = interpolant.getInterpolant();
    PTRef new_root;
    if(substitute){
        logic->varsubstitute(old_root, subst, new_root);
    }
    else{
        new_root = logic->getTerm_true();
    }
//    std::cout << "; Old formula: " << logic->printTerm(old_root) << '\n';
//    std::cout << "; New formula " << logic->printTerm(new_root) << std::endl;
    interpolant.setInterpolant(new_root);
    tt->setBody(new_root);
}
#endif // PRODUCE_PROOF

//FIXME remove this!
string
smtcheck_opensmt2t::quote_varname(const string& varname)
{
    string ans("");
    assert(varname.length() > 0);
    if(varname[0] != '|'){
        ans += '|';
    }
    ans += varname;
    if(varname[varname.length() - 1] != '|'){
        ans += '|';
    }
    return ans;
}

PTRef smtcheck_opensmt2t::substitute(smt_itpt & itp, const std::vector<symbol_exprt> & symbols) {
  Tterm * tterm = itp.getTterm();
  assert(!itp.is_trivial());
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
    PTRef symbol_ptref = this->convert_symbol(symbols[i]);
    subst.insert(argument, PtAsgn(symbol_ptref, l_True));
  }

  // do the actual substitution
  PTRef old_root = tterm->getBody();
  PTRef new_root;
  logic->varsubstitute(old_root, subst, new_root);
  return new_root;
}
