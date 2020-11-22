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

#include <smt2newcontext.h>

#ifdef DISABLE_OPTIMIZATIONS
#include <fstream>
using namespace std;
#include <sstream>
#include <iostream>
#endif

// Free all inner objects
smtcheck_opensmt2t::~smtcheck_opensmt2t()
{
    top_level_formulas.reset();
    assert(top_level_formulas.size() == 0);
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
    //if true const
    if (fr.is_true())
        return true;
    //if false const
    else if (fr.is_false())
        return false;
    //value for boolean expression
    ValPair a_p = mainSolver->getValue(flaref_to_ptref(fr));
    return ((*a_p.val == *true_str) ^ (fr.sign()));
}

//debug: print the formula being inserted:  logic->pp(ptr)
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
/*******************************************************************\
Function:
Purpose:Total Summary for each function call
\*******************************************************************/
void smtcheck_opensmt2t::extract_itp(PTRef ptref, smt_itpt& itp) const
{
  // KE : interpolant adjustments/remove var indices shall come here
  itp.setInterpolant(ptref);
//  std::cout <<";;Total Summary associated with the ptref " << ptref.x << " is: \n" << logic->printTerm(ptref) <<"\n";
}

/*******************************************************************\
Function: smtcheck_opensmt2t::get_interpolant

 Purpose: Core method for computing interpolants. Extracts the symmetric
 interpolant of the specified set of partitions. This method can be called
 only after solving the the formula with an UNSAT result.
\*******************************************************************/
void smtcheck_opensmt2t::get_interpolant(const interpolation_taskt& partition_ids, interpolantst& interpolants) const
{   
  assert(ready_to_interpolate);
  
  const char* msg2 = nullptr;
  config->setOption(SMTConfig::o_verbosity, verbosity, msg2);
  //if (msg2!=nullptr) { free((char *)msg2); msg2=nullptr; } // If there is an error consider printing the msg
  config->setOption(SMTConfig::o_certify_inter, SMTOption(certify), msg2);
  //if (msg2!=nullptr) free((char *)msg2); // If there is an error consider printing the msg
  
  // Set labeling functions
  config->setBooleanInterpolationAlgorithm(itp_algorithm);
  config->setEUFInterpolationAlgorithm(itp_euf_algorithm);
  config->setLRAInterpolationAlgorithm(itp_lra_algorithm);
  if(!itp_lra_factor.empty()) config->setLRAStrengthFactor(itp_lra_factor.c_str());

  if(reduction)
  {
      config->setReduction(1);
      config->setReductionGraph(reduction_graph);
      config->setReductionLoops(reduction_loops);
  }
  
  std::vector<PTRef> itp_ptrefs;
  // iterative call of getSingleInterpolant:
  produceConfigMatrixInterpolants(partition_ids, itp_ptrefs);

//    int atoms;
//    std::cout <<"###summary size: " << itp_ptrefs.size() <<endl;
  for(unsigned i = 0; i < itp_ptrefs.size(); ++i)
  {
      smt_itpt *new_itp = new smt_itpt();
      extract_itp(itp_ptrefs[i], *new_itp);
//      logic->printTerm(itp_ptrefs[i]);
//      char *s = logic->printTerm(itp_ptrefs[i]);
//      std::cout << "Interpolant " << i << " = " << s << '\n';
//      free(s);
//      atoms = getAtoms(itp_ptrefs[i]);
//      std::cout <<"# theory atoms for this sub-summary: " << atoms <<endl;
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
        line = logic->printTerm(ptref);

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
    
    // TEST TO ASSURE THE NAME IS VALID!
    assert(!is_cprover_rounding_mode_var(str) && !is_cprover_builtins_var(str));    
    // MB: the IO_CONST expressions does not follow normal versioning, but why NIL is here?
    bool is_IO = (str.find(CProverStringConstants::IO_CONST) != std::string::npos);
    (void)(is_IO); // MB: to avoid compiler warning about unused variable in Release
//    assert("Error: using non-SSA symbol in the SMT encoding"
//         && (is_L2_SSA_symbol(expr) || is_IO)); // KE: can be new type that we don't take care of yet
    // If appears - please fix the code in partition_target_euqationt
    // DO NOT COMMENT OUT!!!
    return str;
}

/*******************************************************************\
 * 
Function: smtcheck_opensmt2t::store_new_unsupported_var

 Purpose: Keep which expressions are not supported and abstracted from 
 * the smt encoding - for convert purpose only (local use)

\*******************************************************************/
void smtcheck_opensmt2t::store_new_unsupported_var(const exprt& expr, const PTRef var) {
    assert(unsupported_expr2ptrefMap.find(expr) == unsupported_expr2ptrefMap.end());
    unsupported_expr2ptrefMap[expr] = var;
}

/*******************************************************************\

Function: smtcheck_opensmt2t::create_unsupported_uf_call

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

/*******************************************************************\
Function:
Purpose:  Returns all literals that are non-linear expressions
\*******************************************************************/
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
    // initialization of new SummaryTemplate, TODO: the basic should really be set already when interpolant object is created
    auto & tt = interpolant.getTempl();
    interpolant.setDecider(this);

    // prepare the substitution map how OpenSMT expects it
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
        //fill argument of summaries
        tt.addArg(new_var);
    }
    //apply substitution to the interpolant
    PTRef old_root = interpolant.getInterpolant();
    PTRef new_root;
    logic->varsubstitute(old_root, subst, new_root);

//    std::cout << "; Old formula: " << logic->printTerm(old_root) << '\n';
//    std::cout << "; New formula " << logic->printTerm(new_root) << std::endl;
    interpolant.setInterpolant(new_root);
    //the only place to set the body of summary
    tt.setBody(new_root);
}
#endif // PRODUCE_PROOF

PTRef smtcheck_opensmt2t::instantiate(smt_itpt const & smt_itp, const std::vector<symbol_exprt> & symbols) {
    const auto & sumTemplate = smt_itp.getTempl();
    const auto& args = sumTemplate.getArgs();

    // summary is defined as a function over arguments to Bool
    // we need to match the arguments with the symbols and insert_substituted
    // the assumption is that arguments' names correspond to the base names of the symbols
    // and they are in the same order
    // one exception is if global variable is both on input and output, then the out argument was distinguished

    Map<PTRef, PtAsgn, PTRefHash> subst;
    if (symbols.size() != static_cast<std::size_t>(args.size())) {
        throw SummaryInvalidException("Number of interface symbols do not match the summary signature!\n");
        for (size_t i =0 ; i < symbols.size() ; i++) {
            std::string symbol_name{quote_if_necessary(get_symbol_name(symbols[i]).c_str())};
            std::cout << "symbol: " << symbol_name << "\n";
        }
        for (size_t i =0 ; i < args.size() ; i++) {
            std::cout << "\nargs: " <<logic->pp(args[i]) <<std::endl;
        }
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
               << "Expected symbol name: " << symbol_name << "\nName read from summary: " << argument_name <<"\n";
            throw SummaryInvalidException(ss.str());
        }
        PTRef symbol_ptref = expression_to_ptref(symbols[i]);
        subst.insert(argument, PtAsgn(symbol_ptref, l_True));
    }

    // do the actual substitution
    PTRef old_root = sumTemplate.getBody();
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
//    for (int i = 0; i <symbols.size() ; ++i) {
//        std::cout << symbols[i].get_identifier() <<"\n";
//    }
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
        if (logic->isTrue(ptref)) //true only
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

/*
itpt * smtcheck_opensmt2t::create_false_summary(const std::string & function_name) {
    auto ret = new smt_itpt();
    ret->setDecider(this);
    ret->getTempl().setName(function_name);
    ret->getTempl().setBody(logic->getTerm_false());
    //create dummy vars with he size of args
//    for (int i = 0; i < args.size() ; ++i) {
//        std::string str = "dummy" + std::to_string(i);
//        const char * dummy_name = str.c_str();
//        //const char * dummy_name2 = ("dummy" + std::to_string(i)).c_str();
//        PTRef arg = this->mainSolver->getLogic().mkVar(this->get_numeric_sort(), dummy_name);
//        ret->getTempl().addArg(arg);
//    }
    ret->setInterpolant(logic->getTerm_false());
    return ret;
}
*/
/*******************************************************************\
Function:
Purpose:
\*******************************************************************/
bool smtcheck_opensmt2t::isConjunctive(PTRef ptr) const
{
    return logic->isAnd(ptr);
}

bool smtcheck_opensmt2t::isDisjunctive(PTRef ptr) const
{
    return logic->isOr(ptr);
}

/*******************************************************************\
Function: getAtoms
Purpose: counting theory atoms in function summaries
\*******************************************************************/
int smtcheck_opensmt2t::
getAtoms(PTRef tr) const
{
    std::vector<PTRef> atoms;
    //cache of already visited terms
    std::unordered_set<PTRef, PTRefHash> seen;
    std::vector<PTRef> queue;
    queue.push_back(tr);
    while (queue.size() != 0)
    {
        tr = queue.back();
        if (seen.find(tr) != seen.end()) {
            queue.pop_back();
            continue;
        }

        if (logic->isBooleanOperator(tr)) { // is it OR/AND term?  I only need to consider children of connectives, no need for going further (or A B C )
            bool unprocessed_children = false;
//            if(logic->isAnd(tr)) {
//                std::cout << ";;conjunct size is:  "<<  logic->getPterm(tr).size() << "\n" ;//<< logic->printTerm(tr) << "\n";
//            }
            for (int i = 0; i < logic->getPterm(tr).size(); i++)
            {
                PTRef c = logic->getPterm(tr)[i];
                if (seen.find(c) != seen.end()) continue; //found
                else { //if not found
                    queue.push_back(c);
                    unprocessed_children = true;
                }
            }
            if (unprocessed_children == true) continue;
        } // if not boolean operator => it is an atom! A | not A
        queue.pop_back();
        assert(logic->isBooleanOperator(tr) || logic->hasSortBool(tr)); // MB: we should not go past atoms!
//        if (!logic->isBooleanOperator(tr) && logic->hasSortBool(tr)) {
//            atoms.push_back(tr);
//        }
        if (!logic->isBoolAtom(tr) && !logic->isTrue(tr) &&  !logic->isBooleanOperator(tr) && logic->hasSortBool(tr)) {
            atoms.push_back(tr);
 //           std::cout << "tr atom is:  " <<logic->printTerm(tr)<<"\n";
        }
        seen.insert(tr);
    }
    return atoms.size();
}
/*******************************************************************\
Function:
Purpose: create a summary after dropping conjuncts;
 associate PTRef to function name
\*******************************************************************/
smt_itpt * smtcheck_opensmt2t::create_partial_summary( const std::vector<PTRef>& sumArgs_full, const std::string & function_name, const PTRef pref_sub) {
    auto sub_sum = new smt_itpt();
    sub_sum->setDecider(this);
    sub_sum->setInterpolant(pref_sub);
//need to fill Template with name, body, args
    sub_sum->getTempl().setName(function_name);
    //for sub_sum we can use the template of full_sum that was filled in generalize_summary(),
    //copy with new body
    sub_sum->getTempl().setBody(pref_sub);
//  auto sum_full_args = full_sum->getTempl().getArgs(); //args of full-sum are passed via call since it should be deleted from summary_store
//copy args of  full-sum into the args of sub-summary
    for(PTRef arg : sumArgs_full){
        sub_sum->getTempl().addArg(arg);
    }
//    sub_sum->serialize(std::cout);
    return sub_sum;
}

bool smtcheck_opensmt2t::read_formula_from_file(const string & file_name) {
    FILE *f;
    if ((f = fopen(file_name.c_str(), "rt")) == NULL) {
        return false;
    }
    simple_interpretert interpreter(*logic);
    interpreter.interpretFile(f);
    auto const & readTemplates = interpreter.getTemplates();
    for (auto const& funTemplate : readTemplates) {
        this->summary_templates.push_back(funTemplate);
    }
    return true;
}

void smtcheck_opensmt2t::dump_function(ostream & out, const SummaryTemplate & templ) {
    Logic & logic = *this->logic;
    auto name = templ.getName();
    char *quoted_name = logic.protectName(name.c_str());
    out << "(define-fun " << quoted_name << " ( ";
    free(quoted_name);

    const auto& args = templ.getArgs();
    for (PTRef arg: args) {
        char* arg_name = logic.printTerm(arg);
        const char* sort_name = logic.getSortName(logic.getSortRef(arg));
        out << '(' << arg_name << ' ' <<  sort_name << ") ";
        free(arg_name);
    }
    const char* rsort = logic.getSortName(logic.getSortRef(templ.getBody()));
    out << ") " << rsort;
    logic.dumpFormulaToFile(out, templ.getBody(), false, false);
    out << ')' << endl;
}

void simple_interpretert::interpretFile(FILE * file) {
    if (file == nullptr) { return; }
    Smt2newContext context(file);
    int rval = smt2newparse(&context);

    if (rval != 0) { return; }
    const ASTNode* r = context.getRoot();
    for (auto i = r->children->begin(); i != r->children->end(); i++) {
        interpretCommand(**i);
        delete *i;
        *i = nullptr;
    }

}

void simple_interpretert::interpretCommand(ASTNode & node) {
    assert(node.getType() == CMD_T);
    const smt2token cmd = node.getToken();
    switch (cmd.x) {
        case t_declarefun:
        {
            declareFun(node);
            break;
        }
        case t_definefun:
        {
            defineFun(node);
            break;
        }
        case t_declaresort:
        {
            char* name = buildSortName(node);
            if (not logic.containsSort(name)) {
                char* msg;
                logic.declareSort(name, &msg);
            }
            free(name);
            break;
        }
        case t_declareconst:
        {
            declareConst(node);
            break;
        }
        default: // do nothing for other commands
            break;
    }
}

void simple_interpretert::defineFun(ASTNode & node) {
    auto it = node.children->begin();
    ASTNode& name_node = **(it++);
    ASTNode& args_node = **(it++);
    ASTNode& ret_node  = **(it++);
    ASTNode& term_node = **(it++);
    assert(it == node.children->end());

    const char* fname = name_node.getValue();

    // Get the argument sorts
    vec<SRef> arg_sorts;
    vec<PTRef> arg_trs;
    for (auto it2 = args_node.children->begin(); it2 != args_node.children->end(); it2++) {
        string varName = (**it2).getValue();
        auto varC = (**it2).children->begin();
        auto varCC = (**varC).children->begin();
        string sortName = (**varCC).getValue();

        assert(logic.containsSort(sortName.c_str()));
        if (logic.containsSort(sortName.c_str())) {
            arg_sorts.push(logic.getSortRef(sortName.c_str()));
            PTRef pvar = logic.mkVar(arg_sorts.last(), varName.c_str());
            arg_trs.push(pvar);
        }
        else {
            throw std::logic_error("Error in parsing summary file");
        }
    }

    // The return sort
    char* rsort_name = buildSortName(ret_node);
    SRef ret_sort;
    assert(logic.containsSort(rsort_name));
    if (logic.containsSort(rsort_name)) {
        ret_sort = logic.getSortRef(rsort_name);
        free(rsort_name);
    } else {
        throw std::logic_error("Error in parsing summary file");
    }

    sstat status;
    vec<LetFrame> let_branch;
    PTRef tr = parseTerm(term_node, let_branch);
    if (tr == PTRef_Undef) {
        throw std::logic_error("Error in parsing summary file");
    }
    else if (logic.getSortRef(tr) != ret_sort) {
        throw std::logic_error("Error in parsing summary file");
    }
    this->templates.emplace_back();
    auto& t = templates.back();
    t.setName(fname);
    t.setBody(tr);
    for (int i = 0; i < arg_trs.size(); i++) {
        t.addArg(arg_trs[i]);
    }
}

void simple_interpretert::declareFun(ASTNode & node) {
    auto it = node.children->begin();
    ASTNode& name_node = **(it++);
    ASTNode& args_node = **(it++);
    ASTNode& ret_node  = **(it++);
    assert(it == node.children->end());

    const char* fname = name_node.getValue();

    vec<SRef> args;

    char* name = buildSortName(ret_node);

    if (logic.containsSort(name)) {
        SRef sr = logic.getSortRef(name);
        args.push(sr);
        free(name);
    } else {
        throw std::logic_error("Error in parsing summary file");
    }
    for (auto it2 = args_node.children->begin(); it2 != args_node.children->end(); it2++) {
         name = buildSortName(**it2);
        if (logic.containsSort(name)) {
            args.push(logic.getSortRef(name));
            free(name);
        }
        else {
            throw std::logic_error("Error in parsing summary file");
        }
    }
    char* msg;
    SRef rsort = args[0];
    vec<SRef> args2;

    for (int i = 1; i < args.size(); i++)
        args2.push(args[i]);

    SymRef rval = logic.declareFun(fname, rsort, args2, &msg);

    if (rval == SymRef_Undef) {
        throw std::logic_error("Error in parsing summary file");
    }
}

PTRef simple_interpretert::parseTerm(const ASTNode & term, vec<LetFrame> & let_branch) {
    ASTType t = term.getType();
    if (t == TERM_T) {
        const char* name = (**(term.children->begin())).getValue();
        const char* msg;
        vec<SymRef> params;
        PTRef tr = logic.mkConst(name, &msg);
        if (tr == PTRef_Undef) {
            throw std::logic_error("Error in parsing summary file");
        }
        return tr;
    }

    else if (t == QID_T) {
        const char* name = (**(term.children->begin())).getValue();
        PTRef tr = letNameResolve(name, let_branch);
        char* msg = NULL;
        if (tr != PTRef_Undef) {
            return tr;
        }
        vec<PTRef> empty;
        tr = logic.resolveTerm(name, empty, &msg);
        if (tr == PTRef_Undef) {
            throw std::logic_error("Error in parsing summary file");
        }
        free(msg);
        return tr;
    }

    else if ( t == LQID_T ) {
        // Multi-argument term
        auto node_iter = term.children->begin();
        vec<PTRef> args;
        const char* name = (**node_iter).getValue(); node_iter++;
        // Parse the arguments
        for (; node_iter != term.children->end(); node_iter++) {
            PTRef arg_term = parseTerm(**node_iter, let_branch);
            if (arg_term == PTRef_Undef)
                return PTRef_Undef;
            else
                args.push(arg_term);
        }
        assert(args.size() > 0);
        char* msg = NULL;
        PTRef tr = PTRef_Undef;
        tr = logic.resolveTerm(name, args, &msg);
        if (tr == PTRef_Undef) {
            throw std::logic_error("Error in parsing summary file");
        }
        return tr;
    }

    else if (t == LET_T) {
        auto ch = term.children->begin();
        auto vbl = (**ch).children->begin();
        let_branch.push(); // The next scope, where my vars will be defined
        vec<PTRef> tmp_args;
        vec<char*> names;
        // First read the term declarations in the let statement
        while (vbl != (**ch).children->end()) {
            PTRef let_tr = parseTerm(**((**vbl).children->begin()), let_branch);
            if (let_tr == PTRef_Undef) return PTRef_Undef;
            tmp_args.push(let_tr);
            char* name = strdup((**vbl).getValue());
            names.push(name);
            vbl++;
        }
        // Only then insert them to the table
        for (int i = 0; i < tmp_args.size(); i++) {
            if (addLetName(names[i], tmp_args[i], let_branch[let_branch.size()-1]) == false) {
                for (int j = 0; j < names.size(); j++) free(names[j]);
                throw std::logic_error("Error in parsing summary file");
            }
            assert(let_branch[let_branch.size()-1].contains(names[i]));
        }
        ch++;
        // This is now constructed with the let declarations context in let_branch
        PTRef tr = parseTerm(**(ch), let_branch);
        if (tr == PTRef_Undef) {
            for (int i = 0; i < names.size(); i++) free(names[i]);
            throw std::logic_error("Error in parsing summary file");
        }
        let_branch.pop(); // Now the scope is unavailable for us
        for (int i = 0; i < names.size(); i++)
            free(names[i]);
        return tr;
    }
    else {
        throw std::logic_error("Unsupported operation while reading summary file");
    }
    return PTRef_Undef;
}

bool simple_interpretert::addLetName(const char * s, const PTRef tr, LetFrame & frame) {
    if (frame.contains(s)) {
        return false;
    }
    if (logic.hasSym(s) && logic.getSym(logic.symNameToRef(s)[0]).noScoping()) {
        return false;
    }
    frame.insert(s, tr);
    return true;
}

PTRef simple_interpretert::letNameResolve(const char * s, const vec<LetFrame> & frame) const {
    for (int i = frame.size()-1; i >= 0; i--) {
        if (frame[i].contains(s)) {
            PTRef tref = frame[i][s];
            return tref;
        }
    }
    return PTRef_Undef;
}

char * simple_interpretert::buildSortName(ASTNode & n) {
    auto it = n.children->begin();
    char* canon_name;
    int written = asprintf(&canon_name, "%s", (**it).getValue());
    assert(written >= 0); (void)written;
    return canon_name;
}

void simple_interpretert::declareConst(ASTNode & n) {
    auto it = n.children->begin();
    ASTNode& name_node = **(it++);
    it++; // args_node
    ASTNode& ret_node = **(it++);
    const char* fname = name_node.getValue();
    char* name = buildSortName(ret_node);
    SRef ret_sort;
    if (logic.containsSort(name)) {
        ret_sort = logic.getSortRef(name);
        free(name);
    } else {
        free(name);
        throw std::logic_error("Error in parsing summary file");
    }
    PTRef rval = logic.mkConst(ret_sort, fname);
    if (rval == PTRef_Undef) {
        throw std::logic_error("Error in parsing summary file");
    }
}
