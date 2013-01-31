/*******************************************************************\

Module: OpenSMT wrapper for propositional logic. Based on
satcheck_minisat.

Author: Ondrej Sery

\*******************************************************************/

#include <assert.h>

#include <i2string.h>
#include <vector>
#include <iosfwd>
#include <ios>

#include "satcheck_opensmt.h"

#ifndef HAVE_OPENSMT
//#error "Expected HAVE_OPENSMT"
#endif

//#define MAX_OPENSMT_PARTITIONS 63

static unsigned dump_count = 0;

satcheck_opensmtt::satcheck_opensmtt(int verbosity, bool _dump_queries) :
  solver_verbosity(verbosity), dump_queries (_dump_queries), opensmt_ctx(NULL), 
  partition_root_enode(NULL), partition_count(0), ready_to_interpolate(false)
{
  initializeSolver();
}

  
// Initialize the OpenSMT context
void satcheck_opensmtt::initializeSolver() 
{
  if (opensmt_ctx != NULL) {
    freeSolver();
  }
  
  opensmt_ctx = new OpenSMTContext();
  opensmt_ctx->SetLogic("QF_BOOL");
  //opensmt_ctx->SetOption(":verbosity", "1");

  SMTConfig& config = opensmt_ctx->getConfig();
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

  sbool = opensmt_ctx->mkSortBool();
}

// Free all resources related to OpenSMT
void satcheck_opensmtt::freeSolver()
{
    delete opensmt_ctx;
    opensmt_ctx = NULL;
    sbool = NULL;
}

/*******************************************************************\

Function: satcheck_opensmtt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

Enode* satcheck_opensmtt::convert(const bvt &bv)
{
  Enode* tmp = NULL;
  
  for(unsigned i=0; i<bv.size(); i++) {
    const literalt& lit = bv[i];
    Enode* var = enodes[lit.var_no()];

    if (lit.sign()) {
      var = opensmt_ctx->mkCons(var, NULL);
      var = opensmt_ctx->mkNot(var);
    }

    tmp = opensmt_ctx->mkCons(var, tmp);
  }

  return tmp;
}

/*******************************************************************\

Function: satcheck_opensmtt::new_partition

  Inputs:

 Outputs: returns a unique partition id

 Purpose: Begins a partition of formula for latter reference during
 interpolation extraction. All assertions made until
 next call of new_partition() will be part of this partition.

\*******************************************************************/
fle_part_idt satcheck_opensmtt::new_partition()
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

# ifdef MAX_OPENSMT_PARTITIONS
  if (partition_count == MAX_OPENSMT_PARTITIONS) {
    std::string s =
            "OpenSMT does not support more than " +
            i2string(MAX_OPENSMT_PARTITIONS) + "partitions so far.";
    throw s.c_str();
  }
# endif

  return partition_count++;
}


/*******************************************************************\

Function: satcheck_opensmtt::get_interpolant

  Inputs:

 Outputs:

 Purpose: Extracts the symmetric interpolant of the specified set of
 partitions. This method can be called only after solving the
 the formula with an UNSAT result.

\*******************************************************************/
void satcheck_opensmtt::get_interpolant(const interpolation_taskt& partition_ids,
    interpolantst& interpolants, double reduction_timeout) const
{
  assert(ready_to_interpolate);
  
  std::vector<Enode*> itp_enodes;
  itp_enodes.reserve(partition_ids.size());

  // Setup proof reduction
//  SMTConfig& config = opensmt_ctx->getConfig();
  if (reduction_timeout > 0) {
    opensmt_ctx->setReductionTime(reduction_timeout);
    opensmt_ctx->reduceProofGraph();
  } else {
//    config.proof_red_time = 0;
//    config.proof_reduce = 0;
  }

  opensmt_ctx->createProofGraph();
  //std::cout << "set up reduction stuff\n";
  //opensmt_ctx->setNumReductionLoops(2);
  //opensmt_ctx->setNumGraphTraversals(2);
  /*if(config.proof_reduce > 0) */
  //opensmt_ctx->reduceProofGraph();
  opensmt_ctx->setPudlakInterpolation();
  opensmt_ctx->GetInterpolants(partition_ids, itp_enodes);
  opensmt_ctx->deleteProofGraph();

  for (std::vector<Enode*>::iterator it = itp_enodes.begin();
          it != itp_enodes.end(); ++it) {
    Enode* node = (*it);

#   if 0
    std::cout << "OpenSMT interpolant: ";
    node->print(std::cout);
    std::cout << std::endl;
#   endif

    prop_itpt itp;
    extract_itp(node, itp);

#   if 0
    std::cout << "CProver stored interpolant: ";
    itp.print(std::cout);
#   endif

    interpolants.push_back(prop_itpt());
    interpolants.back().swap(itp);
  }
}

/*******************************************************************\

Function: satcheck_opensmtt::can_interpolate

  Inputs:

 Outputs:

 Purpose: Is the solver ready for interpolation? I.e., the solver was used to 
 decide a problem and the result was UNSAT

\*******************************************************************/
bool satcheck_opensmtt::can_interpolate() const 
{
  return ready_to_interpolate;
}

/*******************************************************************\

Function: satcheck_opensmtt::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt satcheck_opensmtt::l_get(literalt a) const
{
  if (a.is_true())
    return tvt(true);
  else if (a.is_false())
    return tvt(false);

  tvt tvtresult(tvt::TV_UNKNOWN);
  lbool lresult = opensmt_ctx->getModel(enodes[a.var_no()]);

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

Function: satcheck_opensmtt::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string satcheck_opensmtt::solver_text()
{
  return "OpenSMT - propositional logic";
}

/*******************************************************************\

Function: satcheck_opensmtt::add_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_opensmtt::add_variables()
{
  enodes.reserve(no_variables());
  
  while (enodes.size() < no_variables()) {
    increase_id();
    const char* vid = id_str.c_str();
    opensmt_ctx->DeclareFun(vid, NULL, sbool);
    Enode* tmp = opensmt_ctx->mkVar(vid, true);
    enodes.push_back(tmp);
    assert (decode_id(vid) == enodes.size()-1);
  }
}

/*******************************************************************\

Function: satcheck_opensmtt::lcnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_opensmtt::lcnf(const bvt &bv)
{
  bvt new_bv;
  Enode* tmp = NULL;
  
  if(process_clause(bv, new_bv))
    return;
    
  // Shortcut for an empty clause
  if(new_bv.empty())
  {
    std::cerr << "WARNING: Outputing an empty clause -> most probably an error due to pointers." << std::endl;
    tmp = opensmt_ctx->mkFalse();
    partition_root_enode = opensmt_ctx->mkCons(tmp, partition_root_enode);
    return;
  }

  add_variables();
  tmp = convert(new_bv);
  tmp = opensmt_ctx->mkOr(tmp);
  partition_root_enode = opensmt_ctx->mkCons(tmp, partition_root_enode);

  clause_counter++;
}

/*******************************************************************\

Function: satcheck_opensmtt::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt satcheck_opensmtt::prop_solve() {
  assert(status != ERROR);
  ready_to_interpolate = false;

  {
    std::string msg =
            i2string(_no_variables) + " variables, " +
            i2string(clause_counter) + " clauses";
    messaget::status(msg);
  }
# ifndef NDEBUG
  std::cout << "OpenSMT - CNF formula (" << _no_variables << " vars., " <<
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
    dump_file += ".smt2";
    opensmt_ctx->DumpToFileFunFrog(dump_file.c_str());
    dump_file = "__sat_config";
    dump_file += i2string(dump_count);
    dump_file += ".cfg";
    std::ofstream os;
    os.open(dump_file.c_str());
    opensmt_ctx->PrintConfig(os);
    os.close();
    ++dump_count;
  }

  std::string msg;

  opensmt_ctx->addCheckSAT();
  opensmt_ctx->executeCommands();
  if (opensmt_ctx->getStatus() == l_True) {
    msg = "SAT checker: negated claim is SATISFIABLE, i.e., does not hold";
    messaget::status(msg);
    status = SAT;
    return P_SATISFIABLE;
  } else if (opensmt_ctx->getStatus() == l_False) {
    ready_to_interpolate = true;
    msg = "SAT checker: negated claim is UNSATISFIABLE, i.e., holds";
    messaget::status(msg);
  } else {
    throw "Unexpected OpenSMT result.";
  }

  status = UNSAT;
  return P_UNSATISFIABLE;
}

/*******************************************************************\

Function: satcheck_opensmtt::set_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_opensmtt::set_assignment(literalt a, bool value)
{
  throw "Unsupported operation";
}

/*******************************************************************\

Function: satcheck_opensmtt::is_in_conflict

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool satcheck_opensmtt::is_in_conflict(literalt a) const
{
  throw "Unsupported operation";
}

/*******************************************************************\

Function: satcheck_opensmtt::set_assumptions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_opensmtt::set_assumptions(const bvt &bv)
{
  throw "Unsupported operation";
}

/*******************************************************************\

Function: satcheck_opensmtt::increase_id

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_opensmtt::increase_id()
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

Function: satcheck_opensmtt::decode_id

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned satcheck_opensmtt::decode_id(const char* id) const
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

Function: satcheck_opensmtt::close_partition

  Inputs:

 Outputs:

 Purpose: Closes the interpolation partition by passing its CNF form
 (collected in partition_root_enode) to the solver.

\*******************************************************************/

void satcheck_opensmtt::close_partition()
{
  assert(partition_root_enode != NULL);
  partition_root_enode = opensmt_ctx->mkAnd(partition_root_enode);
  opensmt_ctx->Assert(partition_root_enode);
  partition_root_enode = NULL;
}

/*******************************************************************\

Function: satcheck_opensmtt::extract_itp

  Inputs:

 Outputs:

 Purpose: Extracts the propositional interpolant from the OpenSMT
 E-node representation.

\*******************************************************************/

void satcheck_opensmtt::extract_itp(const Enode* enode,
  prop_itpt& target_itp) const
{
  enode_cachet cache;
  target_itp.set_no_original_variables(_no_variables);
  target_itp.root_literal = extract_itp_rec(enode, target_itp, cache);
}

/*******************************************************************\

Function: satcheck_opensmtt::extract_itp_rec

  Inputs:

 Outputs:

 Purpose: Extracts the propositional interpolant from the OpenSMT
 E-node representation. Simple recursive implementation.

\*******************************************************************/

literalt satcheck_opensmtt::extract_itp_rec(const Enode* enode,
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
