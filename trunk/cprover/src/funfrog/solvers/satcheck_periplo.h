/*******************************************************************\

Module: PeRIPLO wrapper for propositional logic. Based on
satcheck_minisat.

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_SATCHECK_PERIPLO_H
#define CPROVER_SATCHECK_PERIPLO_H

#include <vector>

#include <solvers/sat/cnf.h>

#include "interpolating_solver.h"
#define PRODUCE_PROOF
#include "PeriploContext.h"

class satcheck_periplot:public cnf_solvert, public interpolating_solvert
{
public:
  satcheck_periplot(int verbosity = 0, bool _dump_queries = false);
  
  virtual ~satcheck_periplot() {
    freeSolver();
  }
  
  virtual resultt prop_solve();
  virtual tvt l_get(literalt a) const;

  virtual void lcnf(const bvt &bv);
  const virtual std::string solver_text();
  virtual void set_assignment(literalt a, bool value);
  // extra MiniSat feature: solve with assumptions
  virtual void set_assumptions(const bvt& _assumptions);
  virtual bool is_in_conflict(literalt a) const;

  virtual bool has_set_assumptions() const { return true; }

  virtual bool has_is_in_conflict() const { return true; }

  // Begins a partition of formula for latter reference during
  // interpolation extraction. All assertions made until
  // next call of new_partition() will be part of this partition.
  //
  // returns a unique partition id
  virtual fle_part_idt new_partition();
  // Extracts the symmetric interpolant of the specified set of
  // partitions. This method can be called only after solving the
  // the formula with an UNSAT result
  virtual void get_interpolant(const interpolation_taskt& partition_ids,
      interpolantst& interpolants,
      double reduction_timeout, int reduction_loops, int reduction_graph);
  virtual void get_interpolant(InterpolationTree*,
      const interpolation_taskt& partition_ids,
      interpolantst& interpolants);
  // Is the solver ready for interpolation? I.e., the solver was used to decide
  // a problem and the result was UNSAT
  virtual bool can_interpolate() const;

  virtual void addAB(const std::vector<unsigned>& symbolsA, const std::vector<unsigned>& symbolsB, const std::vector<unsigned>& symbolsAB)
  {
    std::map<Enode*, icolor_t>* coloring_suggestion;
    coloring_suggestion = new std::map<Enode*, icolor_t>();
    addColors(symbolsA, periplo::I_A, coloring_suggestion);
    addColors(symbolsB, periplo::I_B, coloring_suggestion);
    addColors(symbolsAB, periplo::I_AB, coloring_suggestion);
    coloring_suggestions.push_back(coloring_suggestion);
  };

  virtual void addBitBlastBinding(boolbv_mapt::literal_mapt& map);

  const std::string& get_last_var() { return id_str; }

# ifdef DEBUG_COLOR_ITP
  virtual std::vector<unsigned>& get_itp_symb(unsigned i){ return itp_symbols[i]; }
# endif

protected:
  // Solver verbosity
  unsigned solver_verbosity;
  // Dump all queries?
  bool dump_queries;
  // PeRIPLO API entry point
  PeriploContext* periplo_ctx;
  // Shortcut for the bool sort;
  Snode* sbool;
  // List of clauses that are part of this partition
  Enode* partition_root_enode;
  // Count of the created partitions (the last one is open until a call to
  // prop_solve occurs)
  unsigned partition_count;
  // Mapping from variable indices to their E-nodes in PeRIPLO
  std::vector<Enode*> enodes;
  // Helper string for mangling the variable names
  std::string id_str;
  // Can we interpolate?
  bool ready_to_interpolate;
  
  // Extract interpolant form PeRIPLO Egraph
  void extract_itp(const Enode* enode, prop_itpt& target_itp) const;
  // Cache of already visited interpolant Enodes
  typedef std::map<enodeid_t, literalt> enode_cachet;
  // Simple recursive extraction of clauses from PeRIPLO Egraph
  literalt extract_itp_rec(const Enode* enode, prop_itpt& target_itp, 
    enode_cachet& enode_cache) const;
  
  // Initialize the PeRIPLO context
  void initializeSolver();
  // Free all resources related to PeRIPLO
  void freeSolver();

  void add_variables();
  void increase_id();
  unsigned decode_id(const char* id) const;
  void close_partition();
  Enode* convert(const bvt &bv);
  vector< std::map<Enode*, icolor_t>* > coloring_suggestions;

  void addColors(const std::vector<unsigned>& symbols,
      icolor_t color, std::map<Enode*, icolor_t>* coloring_suggestion);

# ifdef DEBUG_COLOR_ITP
  std::vector<std::vector<unsigned> > itp_symbols;
  std::vector<unsigned> *current_itp;
# endif
};

#endif
