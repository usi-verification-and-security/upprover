/*******************************************************************\

Module: SumO, simple utility for optimizing function summary files.

Author: Ondrej Sery

\*******************************************************************/
#include <cstring>
#include <iostream>
#include <fstream>

#include <time_stopping.h>
#include "function_info.h"
#include "solvers/satcheck_opensmt.h"

void list_summaries(const function_infost& f_infos) {
  for (function_infost::const_iterator it = f_infos.begin();
          it != f_infos.end();
          ++it) {
    const interpolantst& itps = it->second.get_summaries();

    std::cout << "--- function \"" << it->first.c_str() << "\", #summaries: " << itps.size() << std::endl;

    int n = 1;
    for (interpolantst::const_iterator it2 = itps.begin();
            it2 != itps.end();
            ++it2) {
      std::cout << "    summary #" << n++ << ":" << std::endl;
      it2->print(std::cout);
    }
    std::cout << std::endl;
  }
}

bool check_implies(const interpolantt& first, const interpolantt& second) {
  satcheck_opensmtt prop_solver;
  contextt ctx;
  namespacet ns(ctx);

  literalt first_root;
  literalt second_root;
  literalt root;
  
  first_root = first.raw_assert(prop_solver);
  second_root = second.raw_assert(prop_solver);
  
  root = prop_solver.land(first_root, second_root.negation());
  
  prop_solver.l_set_to_true(root);

  fine_timet before, after;
  before=current_time();
  
  propt::resultt res = prop_solver.prop_solve();
  
  after=current_time();
  std::cerr << "SOLVER TIME: "<< time2string(after-before) << std::endl;
  
  if (res == propt::P_UNSATISFIABLE) {
    std::cerr << "UNSAT" << std::endl;
    return true;
  }
  std::cerr << "SAT" << std::endl;
  return false;
}

bool optimize_summaries(const interpolantst& itps_in, interpolantst& itps_out) {
  unsigned n = itps_in.size();
  bool changed = false;
  bool itps_map[n];
  
  // Clear the map first (i.e., no summary has been removed yet)
  for (unsigned i = 0; i < n; ++i) {
    itps_map[i] = true;
  }

  // Remove summaries which are implied by other ones
  for (unsigned i = 0; i < n; ++i) {
    // Skip already removed ones
    if (!itps_map[i])
      continue;
    
    for (unsigned j = 0; j < n; ++j) {
      if (i == j || !itps_map[j])
        continue;
      
      // Do the check
      if (check_implies(itps_in[i], itps_in[j])) {
        std::cerr << "Removing summary #" << j << 
                " (implied by summary #" << i << ")" << std::endl;
        itps_map[j] = false;
        changed = true;
      }
    }
  }
  
  if (!changed)
    return false;
  
  // Prepare the new set
  for (unsigned i = 0; i < n; ++i) {
    if (itps_map[i])
      itps_out.push_back(itps_in[i]);
  }
  return true;
}

void optimize_all_summaries(function_infost& f_infos) {
  interpolantst itps_new;
  
  for (function_infost::iterator it = f_infos.begin();
          it != f_infos.end();
          ++it) {
    const interpolantst& itps = it->second.get_summaries();

    std::cerr << "--- function \"" << it->first.c_str() << "\", #summaries: " << itps.size() << std::endl;

    if (itps.size() <= 1) {
      std::cerr << std::endl;
      continue;
    }

    itps_new.reserve(itps.size());
    if (optimize_summaries(itps, itps_new)) {
      it->second.clear_summaries();
      it->second.add_summaries(itps_new);
      itps_new.clear();
    }
    
    std::cerr << std::endl;
  }
}

void print_help() {
  std::cout <<
          "sumo: SUMmary Optimizer by Ondrej Sery (ondrej.sery@usi.ch)" << std::endl <<
          " - removes redundant function summaries from a given file." << std::endl <<
          std::endl <<
          "Expected usage:" << std::endl <<
          "> sumo {-o|-l} summary_file" << std::endl <<
          "where:" << std::endl <<
          "  --help      print this information" << std::endl <<
          "  --list      list summaries in the summary file" << std::endl <<
          "  --optimize  remove redundant summaries from the summary file" <<
          std::endl << std::endl;
}

int main(int argc, const char** argv) {
  
  bool do_list = argc == 3 && !strcmp(argv[1], "--list");
  bool do_optimize = argc == 3 && !strcmp(argv[1], "--optimize");
  
  if (!do_optimize && !do_list) {
    print_help();
    return strcmp(argv[1], "--help") != 0;
  }
  
  // Load summaries
  function_infost f_infos;
  std::ifstream in;
  
  in.open(argv[2]);
  function_infot::deserialize_infos(in, f_infos);

  if (in.fail()) {
    std::cerr << "ERROR: failed to load the summary file" << std::endl;
    return 1;
  }
  in.close();
  
  // Do the job
  if (do_list) {
    // Only list summaries
    list_summaries(f_infos);
    return 0;
    
  } else if (do_optimize) {
    // Try to optimize
    fine_timet before, after;
    before=current_time();
  
    optimize_all_summaries(f_infos);
    
    after=current_time();
    std::cerr << "TOTAL OPTIMIZATION TIME: "<< time2string(after-before) << std::endl;
    
    function_infot::serialize_infos(argv[2], f_infos);
    return 0;
    
  } else {
    // Wrong command line analysis
    assert(false);
    return 1;
  }
}
