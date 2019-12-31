/*******************************************************************\

Module: Wrapper for OpenSMT2. Based on smtcheck_opensmt2s.

\*******************************************************************/
#include <queue>
#include <unordered_set>

#include "smtcheck_opensmt2.h"
#include "smt_itp.h"
#include "../utils/naming_helpers.h"
#include <funfrog/utils/containers_utils.h>
#include <funfrog/utils/SummaryInvalidException.h>

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

Function: smtcheck_opensmt2t::push_variable

  Inputs: PTRef to store

 Outputs: Literal that has the index of the stored PTRef in ptrefs

 Purpose: Stores new PTRef in mapping between OpenSMT PTRefs and CProver's literals


\*******************************************************************/
FlaRef smtcheck_opensmt2t::ptref_to_flaref(PTRef ptl) {
    assert(getLogic()->hasSortBool(ptl));
    if (getLogic()->isTrue(ptl)) { return const_formula(true); }
	FlaRef fr (ptrefs.size(), false);
	ptrefs.push_back(ptl);
	return fr;
}

// TODO: enhance this to get assignments for any PTRefs, not only for Bool Vars.
bool smtcheck_opensmt2t::is_assignment_true(FlaRef fr) const
{
  if (fr.is_true())
    return true;
  else if (fr.is_false())
    return false;

  ValPair a_p = mainSolver->getValue(flaref_to_ptref(fr));
  return ((*a_p.val == *true_str) ^ (fr.sign()));
}

void smtcheck_opensmt2t::set_to_true(PTRef ptr)
{
    assert(ptr != PTRef_Undef);
    current_partition.push_back(ptr);
}

void smtcheck_opensmt2t::set_equal(FlaRef l1, FlaRef l2){
    vec<PTRef> args;
    PTRef pl1 = flaref_to_ptref(l1);
    PTRef pl2 = flaref_to_ptref(l2);
    args.push(pl1);
    args.push(pl2);
    PTRef ans = logic->mkEq(args);
    set_to_true(ans);
}

FlaRef smtcheck_opensmt2t::land(FlaRef l1, FlaRef l2){
    vec<PTRef> args;
    PTRef pl1 = flaref_to_ptref(l1);
    PTRef pl2 = flaref_to_ptref(l2);
    args.push(pl1);
    args.push(pl2);
    PTRef ans = logic->mkAnd(args);
    return ptref_to_flaref(ans);
}

FlaRef smtcheck_opensmt2t::lor(FlaRef l1, FlaRef l2){
    vec<PTRef> args;
    PTRef pl1 = flaref_to_ptref(l1);
    PTRef pl2 = flaref_to_ptref(l2);
    args.push(pl1);
    args.push(pl2);
    PTRef ans = logic->mkOr(args);
    return ptref_to_flaref(ans);
}

FlaRef smtcheck_opensmt2t::lor(const vector<FlaRef> & bv){
    vec<PTRef> args;
    for(auto lit : bv)
    {
        PTRef tmpp = flaref_to_ptref(lit);
        args.push(tmpp);
    }
    PTRef ans = logic->mkOr(args);
    return ptref_to_flaref(ans);
}

PTRef smtcheck_opensmt2t::constant_to_ptref(const exprt & expr){
    if(is_boolean(expr)){
        bool val;
        if(expr.is_boolean()){
            val = expr.is_true();
        }
        else{
            assert(expr.type().id() == ID_c_bool);
            std::string num(expr.get_string(ID_value));
            assert(num.size() == 8); // if not 8, but longer, please add the case
            val = num.compare("00000000") != 0;
        }
        return constant_bool(val);
    }
    // expr should be numeric constant
    return numeric_constant(expr);
}

#ifdef PRODUCE_PROOF
void smtcheck_opensmt2t::extract_itp(PTRef ptref, smt_itpt& itp) const
{
  // KE : interpolant adjustments/remove var indices shall come here
  itp.setInterpolant(ptref);
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
void smtcheck_opensmt2t::get_interpolant(const interpolation_taskt& partition_ids, interpolantst& interpolants) const
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
  if(!itp_lra_factor.empty()) osmt->getConfig().setLRAStrengthFactor(itp_lra_factor.c_str());

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
    char *s = logic->printTerm(new_itp->getInterpolant());
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
  
  if (!last_partition_closed) {
    close_partition();
  }
  
  insert_top_level_formulas();

  // Dump pre-queries if needed
#ifdef DISABLE_OPTIMIZATIONS
    if (dump_pre_queries) {
        ofstream out_smt;
        //std::cout << ";; Open file " << (pre_queries_file_name + "_X.smt2") << " for pre queries" << std::endl;
        out_smt.open(pre_queries_file_name + "_" + std::to_string(get_unique_index()) + ".smt2");
        logic->dumpHeaderToFile(out_smt);

        // Print the .oites terms
        int size_oite = ite_map_str.size() - 1; // since goes from 0-(n-1)
        int i = 0;
        for (it_ite_map_str iterator = ite_map_str.begin(); iterator != ite_map_str.end(); iterator++) {
            out_smt << "; XXX oite symbol: (" << i << " out of " << size_oite << ") "
                    << iterator->first << endl << "(assert " << iterator->second << "\n)" << endl;
            i++;
        }
        for (int i = 0; i < top_level_formulas.size(); ++i) {
            out_smt << "; XXX Partition: " << (top_level_formulas.size() - i - 1) << endl;
            char * s = logic->printTerm(top_level_formulas[i]);
            out_smt << "(assert \n" << s << "\n)\n";
            free(s);
        }
        out_smt << "(check-sat)\n" << endl;
        out_smt.close();
    }
#endif

    sstat r = mainSolver->check();
 
    // Results from Solver
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

Function: smtcheck_opensmt2t::getSimpleHeader

  Inputs: -

 Outputs: a set of all declarations without variables that used in the smt formula

 Purpose: for summary refinement between theories
 * 
 * TODO: shall work with logic->dumpFunctions(dump_functions); once not empty!

\*******************************************************************/
std::string smtcheck_opensmt2t::getSimpleHeader()
{
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

    auto constants = get_constants();
    for (const PTRef ptref : constants) {
        std::string line{logic->printTerm(ptref)};

        if (line.compare("0") == 0)
            continue;
        if (line.compare("(- 1)") == 0)
            continue;
        ret += "(declare-const " + line + " () "
               + std::string(logic->getSortName(logic->getSortRef(ptref))) + ")\n";
    }
    // Return the list of declares
    return ret;
}


std::set<PTRef> smtcheck_opensmt2t::get_constants() const {
    std::set<PTRef> res;
    std::set<PTRef> seen;

    const auto is_constant = [this](const PTRef ptref) {
        return logic->isConstant(ptref) && !logic->isTrue(ptref) && !logic->isFalse(ptref);
    };
    for(const PTRef ptref : ptrefs)
    {
        collect_rec(is_constant, ptref, res, seen);
    }
    return res;
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
    
    if (is_cprover_builtins_var(str))
        str = unsupported_info.create_new_unsupported_var(expr.type().id().c_str());
    
    //////////////////// TEST TO ASSURE THE NAME IS VALID! ///////////////////// 
    assert(!is_cprover_rounding_mode_var(str) && !is_cprover_builtins_var(str));    
    // MB: the IO_CONST expressions does not follow normal versioning, but why NIL is here?
    bool is_IO = (str.find(CProverStringConstants::IO_CONST) != std::string::npos);
    (void)(is_IO); // MB: to avoid compiler warning about unused variable in Release
//    assert("Error: using non-SSA symbol in the SMT encoding"
//         && (is_L2_SSA_symbol(expr) || is_IO)); // KE: can be new type that we don't take care of yet
    // If appears - please fix the code in partition_target_euqationt
    // DO NOT COMMNET OUT!!! 
    ////////////////////////////////////////////////////////////////////////////

    return str;
}

/*******************************************************************\
 * 
Function: smtcheck_opensmt2t::store_new_unsupported_var

 Inputs: 

 Outputs: 

 Purpose: Keep which expressions are not supported and abstracted from 
 * the smt encoding - for convert purpose only (local use)

\*******************************************************************/
void smtcheck_opensmt2t::store_new_unsupported_var(const exprt& expr, const PTRef var) {
    assert(unsupported_expr2ptrefMap.find(expr) == unsupported_expr2ptrefMap.end());
    unsupported_expr2ptrefMap[expr] = var;
}

/*******************************************************************\

Function: smtcheck_opensmt2t::create_unsupported_uf_call

  Inputs:

 Outputs:

 Purpose:

 *  If not exist yet, creates a new declartion in OpenSMT with 
 *  function name+size of args+type. 
 *  Add a new ptref of the use for this expression
\*******************************************************************/
PTRef smtcheck_opensmt2t::create_unsupported_uf_call(const exprt &expr)
{  
    // Interface function - declare_unsupported_function shall work for any solver 
    // KE: do not refactor and sent args to the method, shall work for any solver!
    std::string decl_str = unsupported_info.declare_unsupported_function(expr);
    if (decl_str.size() == 0)
        return PTRef_Undef;
    
    SymRef decl = unsupported_info.get_declaration(decl_str);
    
    vec<PTRef> args;
    get_function_args(expr, args);
    
    return mkFun(decl,args);
}

/*******************************************************************\

Function: smtcheck_opensmt2t::get_function_args

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
bool smtcheck_opensmt2t::get_function_args(const exprt &expr, vec<PTRef>& args)
{
    // True: at least one arg is unsupported
    bool res = false;
    
    // The we create the new call
    for(auto const & operand : expr.operands())
    {	
        if (is_cprover_rounding_mode_var(operand)) 
        {
            if (expr.id() == ID_mult) continue;
            if (expr.id() == ID_div) continue;
            if (expr.id() == ID_floatbv_mult) continue;
            if (expr.id() == ID_floatbv_div) continue;
        }
        // Skip - we don't need the rounding variable for non-bv logics + assure it is always rounding thing
        // if crush right after this call, add the skip case to the list above

        // Convert
        PTRef cp = expression_to_ptref(operand);
        assert(cp != PTRef_Undef);
        args.push(cp); // Add to call
        
        // Check if unsupported by convert
        char* s_trm = logic->printTerm(cp);
        if (std::string(s_trm).find(HifrogStringUnsupportOpConstants::UNSUPPORTED_VAR_NAME) != std::string::npos)
            res = true;
        free(s_trm);
    }
    
    return res;
}

/*******************************************************************\

Function: smtcheck_opensmt2t::mkFun

  Inputs: function signature in SMTlib with arguments

 Outputs: PTRef of it (with the concrete args)

 Purpose: General mechanism to call uninterpreted functions
          Mainly for a new custom function to smt from summaries

\*******************************************************************/
PTRef smtcheck_opensmt2t::mkFun(SymRef decl, const vec<PTRef>& args)
{
    PTRef ret = logic->mkUninterpFun(decl, args);
    return ret;
}

/*******************************************************************\

Function: smtcheck_opensmt2t::to_string_smtlib_datatype
 * getStringSMTlibDatatype -> to_string_smtlib_datatype

  Inputs:

 Outputs:

 Purpose:

 * For exprt, use typet type = expr.type(); // Get the current type
\*******************************************************************/
std::string smtcheck_opensmt2t::to_string_smtlib_datatype(const typet & type)
{
    if ((type.id()==ID_bool) || (type.id() == ID_c_bool))
        return SMTConstants::SMT_BOOL;
    
    // If not bool we assume it is a number
    SRef name = get_numeric_sort();
    return std::string(logic->getSortName(name));
    
    //return SMTConstants::SMT_UNKNOWN; // Shall not get here
}


/*******************************************************************\

Function: smtcheck_opensmt2t::get_smtlib_datatype
 * getSMTlibDatatype --> get_smtlib_datatype

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
SRef smtcheck_opensmt2t::get_smtlib_datatype(const typet & type)
{
    if ((type.id()==ID_bool) || (type.id() == ID_c_bool))
        return logic->getSort_bool();
    if (is_number(type))
        return get_numeric_sort();
    
    // Assume arrays/pointer assume an numeric presentation
    //std::cout << "Warning: Unknown datatype encountered!\n";
    return get_numeric_sort();
}

#ifdef PRODUCE_PROOF

// Returns all literals that are non-linear expressions
std::set<PTRef> smtcheck_opensmt2t::get_non_linears() const
{
    std::set<PTRef> ret;
    
    // Only for theories that can have non-linear expressions
    if (!can_have_non_linears()) return ret;
    
    // Go over all expressions and search for / or *
    std::set<PTRef> seen;
    const auto is_non_linear = [this](const PTRef ptref){
        return !(logic->isVar(ptref)) && !(logic->isConstant(ptref)) && is_non_linear_operator(ptref);
    };
    for (const PTRef ptref : ptrefs)
    {
        collect_rec(is_non_linear, ptref, ret, seen);
    }
    return ret;
}

//Wrapper
void smtcheck_opensmt2t::generalize_summary(itpt * interpolant, std::vector<symbol_exprt> & common_symbols) {
    auto smt_itp = dynamic_cast<smt_itpt*>(interpolant);
    if(!smt_itp){
        throw std::logic_error{"SMT decider got propositional interpolant!"};
    }
    generalize_summary(*smt_itp, common_symbols);
}

void smtcheck_opensmt2t::generalize_summary(smt_itpt & interpolant, std::vector<symbol_exprt> & common_symbols)
{
    // initialization of new Tterm, TODO: the basic should really be set already when interpolant object is created
    Tterm & tt = interpolant.getTempl();
    interpolant.setDecider(this);

    // prepare the substituition map how OpenSMT expects it
    Map<PTRef,PtAsgn,PTRefHash> subst;
    std::unordered_set<std::string> globals;
    for(const auto& expr : common_symbols){
        // get the original PTRef for this expression
        PTRef original = expression_to_ptref(expr);
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
    logic->varsubstitute(old_root, subst, new_root);

//    std::cout << "; Old formula: " << logic->printTerm(old_root) << '\n';
//    std::cout << "; New formula " << logic->printTerm(new_root) << std::endl;
    interpolant.setInterpolant(new_root);
    tt.setBody(new_root);
}
#endif // PRODUCE_PROOF

PTRef smtcheck_opensmt2t::instantiate(smt_itpt const & smt_itp, const std::vector<symbol_exprt> & symbols) {
    const Tterm & tterm = smt_itp.getTempl();
    const vec<PTRef>& args = tterm.getArgs();

    // summary is defined as a function over arguments to Bool
    // we need to match the arguments with the symbols and insert_substituted
    // the assumption is that arguments' names correspond to the base names of the symbols
    // and they are in the same order
    // one exception is if global variable is both on input and output, then the out argument was distinguished

    Map<PTRef, PtAsgn, PTRefHash> subst;
    if (symbols.size() != static_cast<std::size_t>(args.size())) {
        throw SummaryInvalidException("Number of interface symbols do not match the summary signature!\n");
    }
    for(std::size_t i = 0; i < symbols.size(); ++i){
        std::string symbol_name { get_symbol_name(symbols[i]).c_str() };
        PTRef argument = args[i];
        //Name read from summary
        std::string argument_name { logic->getSymName(argument) };
        if(isGlobalName(argument_name)){
            argument_name = stripGlobalSuffix(argument_name);
        }
        if(symbol_name != argument_name){
            std::stringstream ss;
            ss << "Argument name read from summary do not match expected symbol name!\n"
               << "Expected symbol name: " << symbol_name << "\nName read from summary: " << argument_name;

            throw SummaryInvalidException(ss.str());
        }
        PTRef symbol_ptref = expression_to_ptref(symbols[i]);
        subst.insert(argument, PtAsgn(symbol_ptref, l_True));
    }

    // do the actual substitution
    PTRef old_root = tterm.getBody();
    PTRef new_root;
    logic->varsubstitute(old_root, subst, new_root);
    return new_root;
}
//replaces the function with the summary body(new root)
void smtcheck_opensmt2t::insert_substituted(const itpt & itp, const std::vector<symbol_exprt> & symbols) {
    assert(!itp.is_trivial());
    assert(logic);
    auto const & smt_itp = static_cast<smt_itpt const &> (itp);
    PTRef new_root = instantiate(smt_itp, symbols); //new root is the summary
    // the actual insertion
    this->set_to_true(new_root);

    PTRef old_root = smt_itp.getTempl().getBody();
    ptrefs.push_back(old_root); // MB: needed in sumtheoref to spot non-linear expressions in the summaries
}

void smtcheck_opensmt2t::substitute_negate_insert(const itpt & itp, const std::vector<symbol_exprt> & symbols) {
    assert(!itp.is_trivial());
    assert(logic);
    auto const & smt_itp = static_cast<smt_itpt const &> (itp);
    PTRef new_root = instantiate(smt_itp, symbols); //new root is summary body
    // the actual insertion
    this->set_to_true(logic->mkNot(new_root));
    
    PTRef old_root = smt_itp.getTempl().getBody();  //this is without numbered postfixes
    ptrefs.push_back(old_root); // MB: needed in sumtheoref to spot non-linear expressions in the summaries
}

PTRef smtcheck_opensmt2t::symbol_to_ptref(const exprt & expr) {
    std::string str = extract_expr_str_name(expr); // NOTE: any changes to name - please added it to general method!
    assert(!str.empty());
    assert(expr.is_not_nil()); // MB: this assert should be stronger then the string one, the string one can probably go away
    assert(!(str.compare(CProverStringConstants::NIL) == 0 || str.compare(CProverStringConstants::QUOTE_NIL) == 0));
    if (expr.type().is_nil()) return constant_bool(true); // TODO: MB: check if this can happen
//    MB: it looks like the quoting is unnecessary
//    str = quote_if_necessary(str);
    PTRef symbol_ptref;
    if(is_number(expr.type()))
        symbol_ptref = new_num_var(str);
    else if (is_boolean(expr))
        symbol_ptref = new_bool_var(str);
    else { // Is a function with index, array, pointer
        symbol_ptref = complex_symbol_to_ptref(expr);
    }
    add_symbol_constraints(expr, symbol_ptref);
    return symbol_ptref;
}

PTRef smtcheck_opensmt2t::complex_symbol_to_ptref(const exprt& expr){
    return unsupported_to_var(expr);
}

PTRef smtcheck_opensmt2t::get_from_cache(const exprt & expr) const {
    const auto it = expression_to_ptref_map.find(expr);
    return it == expression_to_ptref_map.end() ? PTRef_Undef : it->second;
}

void smtcheck_opensmt2t::store_to_cache(const exprt & expr, PTRef ptref) {
    assert(expression_to_ptref_map.find(expr) == expression_to_ptref_map.end());
    expression_to_ptref_map[expr] = ptref;
}

exprt smtcheck_opensmt2t::get_value(const exprt & expr) {
    PTRef ptref = get_from_cache(expr);
    if (ptref != PTRef_Undef) {
        // Get the value of the PTRef
        if (logic->isIteVar(ptref)) // true/false - evaluation of a branching
        {
            if (smtcheck_opensmt2t::is_value_from_solver_false(ptref))
                return false_exprt();
            else
                return true_exprt();
        }
        else if (logic->isTrue(ptref)) //true only
        {
            return true_exprt();
        }
        else if (logic->isFalse(ptref)) //false only
        {
            return false_exprt();
        }
        else if (logic->isVar(ptref)) // Constant value
        {
            // Create the value
            irep_idt value =
                    smtcheck_opensmt2t::get_value_from_solver(ptref);

            // Create the expr with it
            constant_exprt tmp;
            tmp.set_value(value);

            return tmp;
        }
        else if (logic->isConstant(ptref))
        {
            // Constant?
            irep_idt value =
                    smtcheck_opensmt2t::get_value_from_solver(ptref);

            // Create the expr with it
            constant_exprt tmp;
            tmp.set_value(value);

            return tmp;
        }
        else
        {
            throw std::logic_error("Unknown case encountered in get_value");
        }
    }
    else // Find the value inside the expression - recursive call
    {
        exprt tmp = expr;

        for(auto & operand : tmp.operands())
        {
            exprt tmp_op = get_value(operand);
            operand.swap(tmp_op);
        }

        return tmp;
    }
}

itpt * smtcheck_opensmt2t::create_stub_summary(const std::string & function_name) {
    auto ret = new smt_itpt();
    ret->setDecider(this);
    ret->getTempl().setName(function_name);
    ret->setInterpolant(logic->getTerm_true());
    return ret;
}
