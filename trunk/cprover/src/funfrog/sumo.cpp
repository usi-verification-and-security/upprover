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

void list_summaries(summary_storet& summary_store, 
        const function_infost& f_infos) 
{
  for (function_infost::const_iterator it = f_infos.begin();
          it != f_infos.end();
          ++it) {
    const summariest& itps = it->second.get_summaries();

    std::cout << "--- function \"" << it->first.c_str() << "\", #summaries: " << itps.size() << std::endl;

    int n = 1;
    for (summariest::const_iterator it2 = itps.begin();
            it2 != itps.end();
            ++it2) {
      std::cout << "    summary #" << n++ << ":" << std::endl;
      summary_store.find_summary(*it2).print(std::cout);
    }
    std::cout << std::endl;
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
  summary_storet summary_store;
  std::ifstream in;
  
  in.open(argv[2]);
  
  summary_store.deserialize(in);
  function_infot::deserialize_infos(in, f_infos);

  if (in.fail()) {
    std::cerr << "ERROR: failed to load the summary file" << std::endl;
    return 1;
  }
  in.close();
  
  // Do the job
  if (do_list) {
    // Only list summaries
    list_summaries(summary_store, f_infos);
    return 0;
    
  } else if (do_optimize) {
    // Try to optimize
    fine_timet before, after;
    before=current_time();
  
    function_infot::optimize_all_summaries(summary_store, f_infos);
    
    after=current_time();
    std::cerr << "TOTAL OPTIMIZATION TIME: "<< time2string(after-before) << std::endl;
    
    std::ofstream out;
  
    out.open(argv[2]);
    summary_store.serialize(out);
    function_infot::serialize_infos(out, f_infos);
    if (out.fail()) {
      std::cerr << "ERROR: failed to save the summary file" << std::endl;
      return 1;
    }
    out.close();
    
    return 0;
    
  } else {
    // Wrong command line analysis
    assert(false);
    return 1;
  }
}
