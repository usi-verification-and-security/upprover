/*******************************************************************\

Module: PeRIPLO wrapper for propositional logic. Based on
satcheck_minisat.

Author: Ondrej Sery

\*******************************************************************/

#include <string.h>
#include <assert.h>

#include <i2string.h>
#include <vector>
#include <iosfwd>
#include <ios>

#include "satcheck_periplo.h"

#ifndef HAVE_OPENSMT
//#error "Expected HAVE_OPENSMT"
#endif

//#define MAX_PeRIPLO_PARTITIONS 63

static unsigned dump_count = 0;

satcheck_periplot::satcheck_periplot(int verbosity, bool _dump_queries,
    int _reduction_loops, int _reduction_graph, bool _tree_interpolation, int _itp_algo, int _proof_trans, bool _check_itp) :
  solver_verbosity(verbosity), dump_queries (_dump_queries),
  reduction_loops(_reduction_loops), reduction_graph(_reduction_graph), tree_interpolation(_tree_interpolation),
  itp_algorithm (_itp_algo), proof_trans(_proof_trans), check_itp (_check_itp),
  periplo_ctx(NULL),
  partition_root_enode(NULL), partition_count(0), ready_to_interpolate(false)
{
  initializeSolver();
}

// Initialize the PeRIPLO context
void satcheck_periplot::initializeSolver()
{
  if (periplo_ctx != NULL) {
    freeSolver();
  }
  periplo_ctx = new PeriploContext();
  periplo_ctx->SetLogic("QF_BOOL");
  //periplo_ctx->SetOption(":verbosity", "1");

  SATConfig& config = periplo_ctx->getConfig();
  config.setProduceModels();
  config.setProduceInter();
  
  config.verbosity = solver_verbosity;
  config.print_proofs_dotty = 0;
  config.proof_red_trans = 1;
  config.proof_red_time = 0; // <-- timeout
  config.proof_reduce = 0;
  //config.proof_reorder_pivots = 0;
  //config.proof_reduce_while_reordering = 0;
  config.proof_set_inter_algo = 0; // McMillan -- the strongest interpolant

  sbool = periplo_ctx->mkSortBool();
}

// Free all resources related to PeRIPLO
void satcheck_periplot::freeSolver()
{
    delete periplo_ctx;
    periplo_ctx = NULL;
    sbool = NULL;
}

/*******************************************************************\

Function: satcheck_periplot::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

Enode* satcheck_periplot::convert(const bvt &bv)
{
  Enode* tmp = NULL;
  for(unsigned i=0; i<bv.size(); i++) {
    const literalt& lit = bv[i];

    Enode* var = enodes[lit.var_no()];

    if (lit.sign()) {
      var = periplo_ctx->mkCons(var, NULL);
      var = periplo_ctx->mkNot(var);
    }

    tmp = periplo_ctx->mkCons(var, tmp);
  }

  return tmp;
}

/*******************************************************************\

Function: satcheck_periplot::new_partition

  Inputs:

 Outputs: returns a unique partition id

 Purpose: Begins a partition of formula for latter reference during
 interpolation extraction. All assertions made until
 next call of new_partition() will be part of this partition.

\*******************************************************************/
fle_part_idt satcheck_periplot::new_partition()
{
//Allowing partitions for havoced functions and fully slices ones
//
//assert(partition_count == 0 || partition_root_enode != NULL);
//  if (partition_count != 0 && partition_root_enode == NULL) {
//    std::cerr << "WARNING: last partition was empty (probably due to slicing)." <<
//            std::endl;
//    // NOTE: The index is reused for the next partition, outer context must
//    // ensure that the previously returned index is not used.
//    partition_count--;
//  }
  
  // Finish the previous partition if any
  if (partition_root_enode != NULL)
    close_partition();

# ifdef MAX_PeRIPLO_PARTITIONS
  if (partition_count == MAX_PeRIPLO_PARTITIONS) {
    std::string s =
            "PeRIPLO does not support more than " +
            i2string(MAX_PeRIPLO_PARTITIONS) + "partitions so far.";
    throw s.c_str();
  }
# endif

  return partition_count++;
}

/*******************************************************************\

Function: satcheck_periplot::setup_reduction

  Inputs:

 Outputs:

 Purpose: Set up corresponded parameters in the interpolating context

\*******************************************************************/
void satcheck_periplot::setup_reduction(){
//std::cout << reduction_loops << " " << reduction_graph <<"\n";

  // Setup proof reduction
  bool do_reduction = false;

  if (reduction_loops > 0){
    periplo_ctx->setNumReductionLoops(reduction_loops);
    do_reduction = true;
  }

  if (reduction_graph > 0){
    periplo_ctx->setNumGraphTraversals(reduction_graph);
    do_reduction = true;
  }

  if (do_reduction){
    periplo_ctx->reduceProofGraph();
  }
}

/*******************************************************************\

Function: satcheck_periplot::setup_interpolation

  Inputs:

 Outputs:

 Purpose: Set up the interpolating algorithm

\*******************************************************************/
void satcheck_periplot::setup_interpolation(){
  switch (itp_algorithm) {
    case 0:
      periplo_ctx->setPudlakInterpolation();
      break;
    case 1:
      periplo_ctx->setMcMillanInterpolation();
      break;
    case 2:
      periplo_ctx->setMcMillanPrimeInterpolation();
      break;
    }
}

/*******************************************************************\

Function: satcheck_periplot::setup_proof_transformation

  Inputs:

 Outputs:

 Purpose: Set up proof transformation

\*******************************************************************/
void satcheck_periplot::setup_proof_transformation(){
  switch (proof_trans) {
    case 1:
      std::cout << "making stronger\n";
      periplo_ctx->enableRestructuringForStrongerInterpolant();
      break;
    case 2:
      std::cout << "making weaker\n";
      periplo_ctx->enableRestructuringForWeakerInterpolant();
      break;
    }
}


/*******************************************************************\

Function: satcheck_periplot::get_interpolant

  Inputs:

 Outputs:

 Purpose: Extracts the symmetric interpolant of the specified set of
 partitions. This method can be called only after solving the
 the formula with an UNSAT result.

\*******************************************************************/
void satcheck_periplot::get_interpolant(const interpolation_taskt& partition_ids,
    interpolantst& interpolants)
{
  assert(ready_to_interpolate);

  std::vector<Enode*> itp_enodes;
  itp_enodes.reserve(partition_ids.size());

  periplo_ctx->createProofGraph();

  setup_reduction();

  // FIXME: dirty cast
  std::vector< std::map<Enode*, icolor_t>* > *ptr;
  ptr = const_cast< std::vector< std::map<Enode*, icolor_t>* > * >(&coloring_suggestions);
  if ((*ptr).size() != 0){
#ifdef FULL_LABELING
    periplo_ctx->setColoringSuggestions(ptr);
    periplo_ctx->setColoringSuggestionsInterpolation();
#endif
  } else {
    setup_interpolation();
  }
  setup_proof_transformation();
  if (check_itp){
    periplo_ctx->setInterpolantCheck();
  }
  periplo_ctx->getInterpolants(partition_ids, itp_enodes);
  periplo_ctx->deleteProofGraph();

  for (std::vector<Enode*>::iterator it = itp_enodes.begin();
          it != itp_enodes.end(); ++it) {
    Enode* node = (*it);

#   if 0
    std::cout << "Periplo interpolant: ";
    node->print(std::cout);
    std::cout << std::endl;
#   endif

    prop_itpt itp;

#   ifdef DEBUG_COLOR_ITP
    current_itp = new std::vector<unsigned> ();
#   endif

    extract_itp(node, itp);

#   ifdef DEBUG_COLOR_ITP
    itp_symbols.push_back(*current_itp);
#   endif

#   if 0
    std::cout << "CProver stored interpolant: ";
    itp.print(std::cout);
#   endif

    interpolants.push_back(prop_itpt());
    interpolants.back().swap(itp);
  }
}

void satcheck_periplot::get_interpolant(InterpolationTree* tree, const interpolation_taskt& partition_ids,
    interpolantst& interpolants)
{
  assert(ready_to_interpolate);

  std::vector<Enode*> itp_enodes;
  itp_enodes.reserve(partition_ids.size());

  periplo_ctx->createProofGraph();

  setup_reduction();

  // FIXME: dirty cast
  std::vector< std::map<Enode*, icolor_t>* > *ptr;
  ptr = const_cast< std::vector< std::map<Enode*, icolor_t>* > * >(&coloring_suggestions);
  if ((*ptr).size() != 0){
#ifdef FULL_LABELING
    periplo_ctx->setColoringSuggestions(ptr);
    periplo_ctx->setColoringSuggestionsInterpolation();
#endif
  } else {
    setup_interpolation();
  }
  setup_proof_transformation();
  if (check_itp){
    periplo_ctx->setInterpolantCheck();
  }
  periplo_ctx->getTreeInterpolants(tree, itp_enodes);
  periplo_ctx->deleteProofGraph();

  for (std::vector<Enode*>::iterator it = itp_enodes.begin();
          it != itp_enodes.end(); ++it) {
    Enode* node = (*it);

#   if 0
    std::cout << "Periplo interpolant: ";
    node->print(std::cout);
    std::cout << std::endl;
#   endif

    prop_itpt itp;

#   ifdef DEBUG_COLOR_ITP
    current_itp = new std::vector<unsigned> ();
#   endif

    extract_itp(node, itp);

#   ifdef DEBUG_COLOR_ITP
    itp_symbols.push_back(*current_itp);
#   endif

#   if 0
    std::cout << "CProver stored interpolant: ";
    itp.print(std::cout);
#   endif

    interpolants.push_back(prop_itpt());
    interpolants.back().swap(itp);
  }
}

/*******************************************************************\

Function: satcheck_periplot::can_interpolate

  Inputs:

 Outputs:

 Purpose: Is the solver ready for interpolation? I.e., the solver was used to 
 decide a problem and the result was UNSAT

\*******************************************************************/
bool satcheck_periplot::can_interpolate() const
{
  return ready_to_interpolate;
}

/*******************************************************************\

Function: satcheck_periplot::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt satcheck_periplot::l_get(literalt a) const
{
  if (a.is_true())
    return tvt(true);
  else if (a.is_false())
    return tvt(false);

  tvt tvtresult(tvt::TV_UNKNOWN);
  lbool lresult = periplo_ctx->getModel(enodes[a.var_no()]);

  if (lresult == l_True)
    tvtresult = tvt(true);
  else if (lresult == l_False)
    tvtresult = tvt(false);
  else
    return tvtresult;
  
  if (a.sign())
    return !tvtresult;

  return tvtresult;
}

/*******************************************************************\

Function: satcheck_periplot::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string satcheck_periplot::solver_text()
{
  return "PeRIPLO - propositional logic";
}

/*******************************************************************\

Function: satcheck_periplot::add_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_periplot::add_variables()
{
  enodes.reserve(no_variables());
  
  while (enodes.size() < no_variables()) {
    increase_id();
    const char* vid = id_str.c_str();
    periplo_ctx->DeclareFun(vid, NULL, sbool);
    Enode* tmp = periplo_ctx->mkVar(vid, true);
    enodes.push_back(tmp);
    assert (decode_id(vid) == enodes.size()-1);
  }
}

/*******************************************************************\

Function: satcheck_periplot::lcnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_periplot::lcnf(const bvt &bv)
{
  bvt new_bv;
  Enode* tmp = NULL;

  if(process_clause(bv, new_bv))
    return;

  // Shortcut for an empty clause
  if(new_bv.empty())
  {
    std::cerr << "WARNING: Outputing an empty clause -> most probably an error due to pointers." << std::endl;
    tmp = periplo_ctx->mkFalse();
    partition_root_enode = periplo_ctx->mkCons(tmp, partition_root_enode);
    return;
  }

  add_variables();
  tmp = convert(new_bv);
  tmp = periplo_ctx->mkOr(tmp);
  partition_root_enode = periplo_ctx->mkCons(tmp, partition_root_enode);

  clause_counter++;
}

/*******************************************************************\

Function: satcheck_periplot::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt satcheck_periplot::prop_solve() {
  assert(status != ERROR);
  ready_to_interpolate = false;

  {
    std::string msg =
            i2string(_no_variables) + " variables, " +
            i2string(clause_counter) + " clauses";
    messaget::status(msg);
  }
# ifndef NDEBUG
  std::cout << "PeRIPLO - CNF formula (" << _no_variables << " vars., " <<
          clause_counter << " cl.)" << std::endl;
# endif

  add_variables();

  if (partition_root_enode != NULL) {
    close_partition();
  }
  // Dump the SAT query and configuration
  if (dump_queries)
  {
    std::string dump_file("__sat_query");
    dump_file += i2string(dump_count);
    dump_file += ".SMT2";
    periplo_ctx->DumpToFileFunFrog(dump_file.c_str());
    dump_file = "__sat_config";
    dump_file += i2string(dump_count);
    dump_file += ".cfg";
    std::ofstream os;
    os.open(dump_file.c_str());
    periplo_ctx->PrintConfig(os);
    os.close();
    ++dump_count;
  }

  std::string msg;

  //periplo_ctx->SetOption(":verbosity", "1");
  periplo_ctx->addCheckSAT();
  periplo_ctx->executeCommands();
  if (periplo_ctx->getStatus() == l_True) {
    msg = "SAT checker: negated claim is SATISFIABLE, i.e., does not hold";
    messaget::status(msg);
    status = SAT;
    return P_SATISFIABLE;
  } else if (periplo_ctx->getStatus() == l_False) {
    ready_to_interpolate = true;
    msg = "SAT checker: negated claim is UNSATISFIABLE, i.e., holds";
    messaget::status(msg);
  } else {
    throw "Unexpected PeRIPLO result.";
  }

  status = UNSAT;
  return P_UNSATISFIABLE;
}

/*******************************************************************\

Function: satcheck_periplot::set_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_periplot::set_assignment(literalt a, bool value)
{
  throw "Unsupported operation";
}

/*******************************************************************\

Function: satcheck_periplot::is_in_conflict

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool satcheck_periplot::is_in_conflict(literalt a) const
{
  throw "Unsupported operation";
}

/*******************************************************************\

Function: satcheck_periplot::set_assumptions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_periplot::set_assumptions(const bvt &bv)
{
  throw "Unsupported operation";
}

/*******************************************************************\

Function: satcheck_periplot::increase_id

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_periplot::increase_id()
{
  unsigned i = 0;

  while (i < id_str.length() && id_str[i] == 'Z') {
    id_str[i++] = 'A';
  }

  if (i < id_str.length()) {
    id_str[i]++;
  } else {
    id_str.append("A");
  }
}

/*******************************************************************\

Function: satcheck_periplot::decode_id

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned satcheck_periplot::decode_id(const char* id) const
{
  unsigned base = 1;
  unsigned i = 0;

  while (*id != 0) {
    i += base * (*id++ - 'A' + 1);
    base *= 'Z'-'A'+1;
  }
  return i-1;
}

/*******************************************************************\

Function: satcheck_periplot::close_partition

  Inputs:

 Outputs:

 Purpose: Closes the interpolation partition by passing its CNF form
 (collected in partition_root_enode) to the solver.

\*******************************************************************/

void satcheck_periplot::close_partition()
{
  assert(partition_root_enode != NULL);
  partition_root_enode = periplo_ctx->mkAnd(partition_root_enode);
  //std::cout << "## Asserting formula: " << partition_root_enode << endl;
  periplo_ctx->Assert(partition_root_enode);

//  std::cout<< "&&&&: "<< partition_root_enode << "\n";
  partition_root_enode = NULL;
}

/*******************************************************************\

Function: satcheck_periplot::extract_itp

  Inputs:

 Outputs:

 Purpose: Extracts the propositional interpolant from the PeRIPLO
 E-node representation.

\*******************************************************************/

void satcheck_periplot::extract_itp(const Enode* enode,
  prop_itpt& target_itp) const
{
  enode_cachet cache;
  target_itp.set_no_original_variables(_no_variables);
  target_itp.root_literal = extract_itp_rec(enode, target_itp, cache);
}

/*******************************************************************\

Function: satcheck_periplot::extract_itp_rec

  Inputs:

 Outputs:

 Purpose: Extracts the propositional interpolant from the PeRIPLO
 E-node representation. Simple recursive implementation.

\*******************************************************************/

literalt satcheck_periplot::extract_itp_rec(const Enode* enode,
  prop_itpt& target_itp, enode_cachet& enode_cache) const
{
  enode_cachet::const_iterator cached_it = enode_cache.find(enode->getId());
  literalt result;

  if (cached_it != enode_cache.end()) {
    return cached_it->second;
  }

  if (enode->isTerm()) {
    switch (enode->getCar()->getId()) {
    case ENODE_ID_TRUE:
      result = const_literal(true);
      break;
    case ENODE_ID_FALSE:
      result = const_literal(false);
      break;
    case ENODE_ID_AND:
      assert(enode->getArity() == 2);
      result = target_itp.land(
              extract_itp_rec(enode->get1st(), target_itp, enode_cache),
              extract_itp_rec(enode->get2nd(), target_itp, enode_cache));
      break;
    case ENODE_ID_OR:
      assert(enode->getArity() == 2);
      result = target_itp.lor(
              extract_itp_rec(enode->get1st(), target_itp, enode_cache),
              extract_itp_rec(enode->get2nd(), target_itp, enode_cache));
      break;
    case ENODE_ID_NOT:
      assert(enode->getArity() == 1);
      result = target_itp.lnot(
              extract_itp_rec(enode->get1st(), target_itp, enode_cache));
      break;
    default:
      if (enode->isAtom()) {
        // Atom must be a prop. variable
        assert(enode->getArity() == 0 && enode->getCar()->isSymb());

#   ifdef DEBUG_COLOR_ITP
        unsigned var_no = 0;
        while(var_no < enodes.size()){
          if (enodes[var_no] == enode){
            break;
          }
          var_no++;
        }
        current_itp->push_back(var_no);
#   endif

        result.set(decode_id(enode->getCar()->getNameFullC()), false);
      } else {
        throw "Unexpected Enode term type in the interpolant.";
      }
    }
  } else {
    throw "Unexpected Enode type in the interpolant.";
  }

  enode_cache.insert(enode_cachet::value_type(enode->getId(), result));
  return result;
}

void satcheck_periplot::addColors(const std::vector<unsigned>& symbols,
    icolor_t color, std::map<Enode*, icolor_t>* coloring_suggestion)
{
  for (unsigned i = 0; i < symbols.size(); i++){
    (*coloring_suggestion)[enodes[symbols[i]]] = color;
  }
}

void satcheck_periplot::addBitBlastBinding(boolbv_mapt::literal_mapt& map){
  std::vector<Enode*> v;
  for (unsigned i = 0; i < map.size(); i++){
    if(map[i].l.var_no() < enodes.size()){
      v.push_back(enodes[map[i].l.var_no()]);
    }
  }
  periplo_ctx->addBitBlastBinding(v);
}
