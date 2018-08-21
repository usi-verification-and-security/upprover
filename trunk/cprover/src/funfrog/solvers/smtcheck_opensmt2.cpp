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

// Free all inner objects
smtcheck_opensmt2t::~smtcheck_opensmt2t()
{
    top_level_formulas.reset();
    assert(top_level_formulas.size() == 0);
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
  if (current_partition != nullptr)
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

literalt smtcheck_opensmt2t::lconst(bool val)
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
    (void)l;
    assert(l.var_no() != literalt::unused_var_no()); // KE: for cmake warnings
    
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
        return lconst(expr.is_true());
    } else if (expr.type().id() == ID_c_bool) { // KE: New Cprover code - patching
        std::string num(expr.get_string(ID_value));
        assert(num.size() == 8); // if not 8, but longer, please add the case
        return lconst(num.compare("00000000") != 0);
        //std::cout << "Check? " << (num.compare("00000000") != 0) << " for string " << num << std::endl;
    } else {
        return lconst_number(expr);
    }
}

#ifdef PRODUCE_PROOF
void smtcheck_opensmt2t::extract_itp(PTRef ptref, smt_itpt& itp) const
{
  // KE : interpolant adjustments/remove var indices shall come here
  itp.setInterpolant(ptref);
}

// helper interpolation method taken from opensmt
void smtcheck_opensmt2t::produceConfigMatrixInterpolants (const std::vector< std::vector<int> > &configs, std::vector<PTRef> &interpolants)
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
  
  const char* msg2 = nullptr;
  osmt->getConfig().setOption(SMTConfig::o_verbosity, verbosity, msg2);
  //if (msg2!=nullptr) { free((char *)msg2); msg2=nullptr; } // If there is an error consider printing the msg
  osmt->getConfig().setOption(SMTConfig::o_certify_inter, SMTOption(certify), msg2);
  //if (msg2!=nullptr) free((char *)msg2); // If there is an error consider printing the msg
  
  // Set labeling functions
  osmt->getConfig().setBooleanInterpolationAlgorithm(itp_algorithm);
  osmt->getConfig().setEUFInterpolationAlgorithm(itp_euf_algorithm);
  osmt->getConfig().setLRAInterpolationAlgorithm(itp_lra_algorithm);
  if(itp_lra_factor != nullptr) osmt->getConfig().setLRAStrengthFactor(itp_lra_factor);

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

  std::vector<PTRef> itp_ptrefs;

  // iterative call of getSingleInterpolant:
  produceConfigMatrixInterpolants(partition_ids, itp_ptrefs);

  solver.deleteProofGraph();

  for(unsigned i = 0; i < itp_ptrefs.size(); ++i)
  {
      smt_itpt *new_itp = new smt_itpt();
      extract_itp(itp_ptrefs[i], *new_itp);
      interpolants.push_back(new_itp);

#ifdef DEBUG_SMT_ITP
    char *s = logic->printTerm(interpolants.back()->getInterpolant());
    std::cout << "Interpolant " << i << " = " << s << '\n';
    free(s);
    s=nullptr;
#endif
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
#endif //PRODUCE PROOF

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
  
  if (current_partition != nullptr) {
    close_partition();
  }

#ifdef DISABLE_OPTIMIZATIONS
  ofstream out_smt;
  std::string file;
  if (dump_pre_queries) {
    file=pre_queries_file_name+"_"+std::to_string(get_dump_current_index())+".smt2";
    out_smt.open(file); 
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
    char *msg = nullptr;
    for(int i = pushed_formulas; i < top_level_formulas.size(); ++i) {
#ifdef DISABLE_OPTIMIZATIONS
        if (dump_pre_queries)
        {
            out_smt << "; XXX Partition: " << (top_level_formulas.size() - i - 1) << endl;
            char* s = logic->printTerm(top_level_formulas[i]);
            out_smt << "(assert \n" << s << "\n)\n";
            free(s);
            s=nullptr;
        }
#endif
        mainSolver->insertFormula(top_level_formulas[i], &msg);
        if (msg != nullptr) {
            free(msg); // If there is an error, consider print msg
            msg = nullptr;
        }
    }
 
#ifdef DISABLE_OPTIMIZATIONS   
    if (dump_pre_queries) {
        out_smt << "(check-sat)\n" << endl;
        out_smt.close();
    }
#endif    

    pushed_formulas = top_level_formulas.size();
    sstat r = mainSolver->check();

    // Inc. Mode Info.
    if ((no_literals_last_solved != 0) && (no_literals_last_solved < no_literals))
        std::cout << ";; Using OpenSMT Incremental Mode with "
                  << (no_literals - no_literals_last_solved) << " additional literals"
                  << std::endl;
    no_literals_last_solved = no_literals;

    // Results from Solver
    if (r == s_True) {
        return true;
    } else if (r == s_False && has_overappox_mapping()) {
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
  assert(current_partition != nullptr);
  if (partition_count > 0){
    if (current_partition->size() > 1){
      PTRef pand = logic->mkAnd(*current_partition);
#ifdef DEBUG_SMT2SOLVER
      char* s= logic->printTerm(pand);
      std::cout << "; Pushing to solver: " << s << endl;
      free(s); s=nullptr;
#endif
      top_level_formulas.push(pand);
    } else if (current_partition->size() == 1){
      PTRef pand = (*current_partition)[0];
#ifdef DEBUG_SMT2SOLVER
      std::cout << "Trivial partition (terms size = 1): " << partition_count << "\n";
      char* s= logic->printTerm(pand);
      std::cout << "; Pushing to solver: " << s << endl;
      free(s); s=nullptr;
#endif
      top_level_formulas.push(pand);
    } /*else {
      // GF: adding (assert true) for debugging only
      top_level_formulas.push(logic->getTerm_true());
    } */
  }

  current_partition = nullptr;
}

/*******************************************************************\

Function: smtcheck_opensmt2t::getSimpleHeader

  Inputs: -

 Outputs: a set of all declarations without variables that used in the smt formula

 Purpose: for summary refinement between theories
 * 
 * TODO: shall work with logic->dumpFunctions(dump_functions); once not empty!

\*******************************************************************/
std::string smtcheck_opensmt2t::getSimpleHeader()
{
    // Never add twice the same declare
    std::set<PTRef>* was = new std::set<PTRef>();

    // This code if works, replace the remove variable section
    //std::stringstream dump_functions;
    //logic->dumpFunctions(dump_functions);
    //std::cout << dump_functions.str() << std::endl;
    //assert(dump_functions.str().empty()); // KE: show me when it happens!
    
    // Get the original header
    std::stringstream dump;
    logic->dumpHeaderToFile(dump);
    if (dump.str().empty())
        return "";
 
    // Remove the Vars   
    std::string line;
    std::string ret = "";
    // Skip the first line always!
    std::getline(dump,line,'\n');
    // take only const and function definitions
    while(std::getline(dump,line,'\n')){
        if (line.find(".oite")!=std::string::npos)
            continue;
        if (line.find("|nil|")!=std::string::npos)
            continue;
        if (line.find("nil () Bool")!=std::string::npos)
            continue;
        if (line.find(HifrogStringUnsupportOpConstants::UNSUPPORTED_VAR_NAME)==std::string::npos)
        {       
            if (line.find("|")!=std::string::npos) 
                continue;
            if (line.find("declare-sort Real 0")!=std::string::npos) 
                continue;
        }
        
        // Function declarations and unsupported vars only
        ret += line + "\n";
    }

    // Add constants:
    for(it_literals it = literals.begin(); it != literals.end(); it++)
    {
        if ((logic->isConstant(*it)) && (was->count(*it) < 1) 
                && !logic->isFalse(*it) && !logic->isTrue(*it))
        {
            char* name = logic->printTerm(*it);
            std::string line(name);
            free(name); name=nullptr;
            
            if (line.compare("0") == 0) 
                continue;
            if (line.compare("(- 1)") == 0) 
                continue;

            ret += "(declare-const " + std::string(line) + " () " 
                        + std::string(logic->getSortName(logic->getSortRef(*it))) + ")\n";
            was->insert(*it);
        }
    }
    
    // Return the list of declares
    return ret;
}

/*******************************************************************\

Function: smtcheck_opensmt2t::extract_expr_str_name

  Inputs: expression that is a var

 Outputs: a string of the name

 Purpose: assure we are extracting the name correctly and in one place.

\*******************************************************************/
std::string smtcheck_opensmt2t::extract_expr_str_name(const exprt &expr)
{
    std::string str = normalize_name(expr);
    
    //////////////////// TEST TO ASSURE THE NAME IS VALID! /////////////////////
    assert(!is_cprover_rounding_mode_var(str) && !is_cprover_builtins_var(str));    
    // MB: the IO_CONST expressions does not follow normal versioning, but why NIL is here?
    bool is_nil_or_symex = (str.compare(NIL) == 0) || (str.find(CProverStringConstants::IO_CONST) != std::string::npos);
    assert("Error: using non-SSA symbol in the SMT encoding"
         && (is_L2_SSA_symbol(expr) || is_nil_or_symex)); // KE: can be new type that we don't take care of yet
    // If appears - please fix the code in smt_partition_target_euqationt
    // DO NOT COMMNET OUT!!! 
    ////////////////////////////////////////////////////////////////////////////

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
    std::cout << "; XXX SMT-lib --> Current Logic Translation XXX" << std::endl;
    std::cout << "; Declarations from two source: if there is no diff use only one for testing the output" << std::endl;
    std::cout << "; Declarations from Hifrog :" << std::endl;
    for(it_var_set_str iterator = var_set_str.begin(); iterator != var_set_str.end(); iterator++) {
            std::cout << "(declare-fun " << *iterator << ")" << std::endl;
    }
    std::cout << "; Declarations from OpenSMT2 :" << std::endl;
#endif
    logic->dumpHeaderToFile(std::cout);
    std::cout << "(assert\n  (and" << std::endl;
    for(int i = 0; i < top_level_formulas.size(); ++i) {
        PTRef tmp;
        logic->conjoinExtras(top_level_formulas[i], tmp);
        char *s = logic->printTerm(tmp);
        std::cout << "; XXX Partition: " << i << std::endl << "    " << s << std::endl;
        free(s); s=nullptr;
    }

    // If code - once needed uncomment this debug flag in the header
#ifdef DISABLE_OPTIMIZATIONS
    int size_oite = ite_map_str.size()-1; // since goes from 0-(n-1) 
    int i = 0;
    for(it_ite_map_str iterator = ite_map_str.begin(); iterator != ite_map_str.end(); iterator++) {
        std::cout << "; XXX oite symbol: (" << i << " out of " << size_oite << ") "
                << iterator->first << std::endl << iterator->second << std::endl;
        i++;
    }
#endif
    std::cout << "))" << std::endl << "(check-sat)" << std::endl;
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
 * 
Function: smtcheck_opensmt2t::store_new_unsupported_var

 Inputs: 

 Outputs: 

 Purpose: Keep which expressions are not supported and abstracted from 
 * the smt encoding

\*******************************************************************/
literalt smtcheck_opensmt2t::store_new_unsupported_var(const exprt& expr, const PTRef var, bool push_var) { 
    char *s = logic->printTerm(var);
    unsupported_info.store_new_unsupported_var(expr,std::string(s));  
    #ifdef DEBUG_LATTICE // Debug only - in if for better performance     
        cout << "Expression " << s << " will be refine the operator " 
              << expr.id() << " with " << expr.operands().size() << " operands." 
              << endl;
    #endif
    free(s);
    s=nullptr;
        
    if (push_var)
        return push_variable(var);
    else 
        return const_literal(true);
}

/*******************************************************************\

Function: smtcheck_opensmt2t::get_smt_func_decl

 Inputs: name of the function and its signature

 Outputs: the function declarations

 Purpose: to create new custom function to smt from summaries

\*******************************************************************/
SymRef smtcheck_opensmt2t::get_smt_func_decl(const char* op, SRef& in_dt, vec<SRef>& out_dt) {
    char *msg=nullptr;
    SymRef ret = logic->declareFun(op, in_dt, out_dt, &msg, true);
    if (msg != nullptr) free(msg);

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
    
    // Keep the list of already declared
    static std::map<std::string,SymRef> decl_uninterperted_func; // Inner use only
    
    // Define the function if needed and check it is OK
    SymRef decl = SymRef_Undef;
    if (decl_uninterperted_func.count(key_func) == 0) {
        decl = get_smt_func_decl(func_id.c_str(), out, args_decl);
        decl_uninterperted_func.insert(std::pair<std::string, SymRef> (key_func,decl));
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
    char *msg=nullptr;
    PTRef ret = logic->mkFun(decl, args, &msg);
    if (msg != nullptr) free(msg);  
    
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

    literalt l_unsupported = lunsupported2var(expr);
    PTRef var = literals[l_unsupported.var_no()];
    return logic->getSortRef(var);
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

// Returns all literals that are non-linear expressions
std::set<PTRef>* smtcheck_opensmt2t::get_non_linears()
{
    std::set<PTRef>* ret = new std::set<PTRef>();
    
    // Only for theories that can have non-linear expressions
    if (!can_have_non_linears()) return ret;
    
    // Go over all expressions and search for / or *
    std::set<PTRef>* was = new std::set<PTRef>();
    for(it_literals it = literals.begin(); it != literals.end(); it++)
    {
        if ((was->count(*it) < 1) && (ret->count(*it) < 1) && !(logic->isVar(*it)) && !(logic->isConstant(*it)))
        {
            if (is_non_linear_operator(*it))
            {
                ret->insert(*it);
            }
        }
        was->insert(*it);
    }

    delete(was);
    return ret;
}

// FIXME: move to smt_itpt class
void smtcheck_opensmt2t::generalize_summary(itpt &interpolant_in, std::vector<symbol_exprt> &common_symbols,
                                            const std::string &fun_name, bool substitute)
{
    auto & interpolant = static_cast<smt_itpt &> (interpolant_in);
    
    // Right now the term is not set, hence the assert, but this should actually be set somewhere else
    if(is_cprover_initialize_method(fun_name)){
        throw std::logic_error("Summary generalize should not be called for CPROVER initialize method!");
    }
    // initialization of new Tterm, TODO: the basic should really be set already when interpolant object is created
    Tterm & tt = interpolant.getTempl();
    tt.setName(fun_name.c_str());
    interpolant.setDecider(this);


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
        tt.addArg(new_var);
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
    tt.setBody(new_root);
}
#endif // PRODUCE_PROOF

void smtcheck_opensmt2t::insert_substituted(const itpt & itp, const std::vector<symbol_exprt> & symbols) {
  assert(logic);
  auto const & smt_itp = static_cast<smt_itpt const &> (itp);
  assert(!smt_itp.is_trivial());
  
  const Tterm & tterm = smt_itp.getTemplConst();
  const vec<PTRef>& args = tterm.getArgs();

  // summary is defined as a function over arguments to Bool
  // we need to match the arguments with the symbols and insert_substituted
  // the assumption is that arguments' names correspond to the base names of the symbols
  // and they are in the same order
  // one exception is if global variable is both on input and output, then the out argument was distinguished

  Map<PTRef, PtAsgn, PTRefHash> subst;
  assert(symbols.size() == static_cast<std::size_t>(args.size()));
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
  PTRef old_root = tterm.getBody();
  PTRef new_root;
  logic->varsubstitute(old_root, subst, new_root);
  this->set_to_true(new_root);
}

/*******************************************************************\

Function: smtcheck_opensmt2t::lvar

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
literalt smtcheck_opensmt2t::lvar(const exprt &expr)
{
    // IF code, set to be unsupported
    if (expr.type().id()==ID_code) {
        return lunsupported2var(expr);
    }

    // Else continue as before
    
    // NOTE: any changes to name - please added it to general method!
    std::string str = quote_if_necessary(extract_expr_str_name(expr)); 
    assert(str.size() > 0);

    // Nil is a special case - don't create a var but a val of true
    if (str.compare(NIL) == 0) return lconst(true);
    if (str.compare(QUOTE_NIL) == 0) return lconst(true);
    if (expr.type().is_nil()) return lconst(true);

#ifdef SMT_DEBUG
	cout << "; (lvar) Create " << str << endl;
#endif
             
    // Else if it is really a var, continue and declare it!
    bool is_defined = (is_number(expr.type()) || (expr.is_boolean()) || (expr.type().id() == ID_c_bool));
    PTRef var = is_defined ? evar(expr, str) : literals[lunsupported2var(expr).var_no()];
    literalt l = push_variable(var); // Keeps the new PTRef + create for it a new index/literal
    
    if (!is_defined) // Is a function with index, array, pointer
    {   
#ifdef SMT_DEBUG
    	cout << "EXIT WITH ERROR: Arrays and index of an array operator have no support yet in the UF version (token: "
    			<< expr.type().id() << ")" << endl;
    	assert(false); // No support yet for arrays
#else
        // TODO: make it work for unsupported data types
        // Add new equation of an unknown function (acording to name)
        //PTRef var_eq = create_equation_for_unsupported(expr);
        //set_to_true(logic->mkEq(ptl,var_eq)); // (= |hifrog::c::unsupported_op2var#0| (op operand0 operand1)) 
#endif
    }

#ifdef DISABLE_OPTIMIZATIONS
    std::string add_var = str + " () " + string(logic->getSortName(logic->getSortRef(var)));
    if (var_set_str.end() == var_set_str.find(add_var)) 
        var_set_str.insert(add_var);
#endif

    return l;
}
