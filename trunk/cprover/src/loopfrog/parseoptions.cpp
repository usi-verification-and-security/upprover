/*******************************************************************\

 Module: Command Line Parsing

 Author: Daniel Kroening, kroening@kroening.com
         CM Wintersteiger

\*******************************************************************/

#include <config.h>

#include <iostream>
#include <fstream>

#include <sys/time.h>
#include <sys/stat.h>
#ifndef _WIN32
#include <sys/resource.h>
#else
#include <io.h>
#endif

#include <message.h>
#include <context.h>
#include <i2string.h>
#include <std_expr.h>
#include <arith_tools.h>
#include <prefix.h>
#include <time_stopping.h>

#include <goto-programs/read_goto_binary.h>
#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_function_pointers.h>
#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/goto_check.h>
#include <goto-programs/string_instrumentation.h>
#include <goto-programs/string_abstraction.h>
#include <goto-programs/slicer.h>
#include <goto-programs/show_claims.h>
#include <goto-programs/remove_unused_functions.h>

#include <pointer-analysis/add_failed_symbols.h>
#include <pointer-analysis/value_set_analysis.h>
#include <pointer-analysis/value_set_analysis_fi.h>
#include <pointer-analysis/value_set_analysis_fivr.h>
#include <pointer-analysis/value_set_analysis_fivrns.h>
#include <pointer-analysis/goto_program_dereference.h>

#include "version.h"
#include "parseoptions.h"
#include "loop_summarizer.h"
#include "string_summarization.h"
#include "value_set_alloc_adaptor.h"
#include "memstat.h"
#include "replace_malloc.h"
#include "program_compression.h"
#include "check_claims.h"
#include "loopstore.h"
#include "transform_loops.h"
#include "inlined_claims.h"
#include "symex_assertion.h"
#include "invariant_propagation_adaptor.h"
#include "languages.h"

/*******************************************************************

 Function: loopfrog_parseoptionst::loopfrog_parseoptionst

 Inputs:

 Outputs:

 Purpose: constructor

 \*******************************************************************/

loopfrog_parseoptionst::loopfrog_parseoptionst(int argc, const char **argv):
  parseoptions_baset(LOOPFROG_OPTIONS, argc, argv),
  language_uit("LOOPFROG" LOOPFROG_VERSION, cmdline)
{
}

/*******************************************************************

 Function: loopfrog_parseoptionst::doit

 Inputs:

 Outputs:

 Purpose: invoke main modules

 \*******************************************************************/

int loopfrog_parseoptionst::doit()
{
  if (config.set(cmdline))
  {
    usage_error();
    exit(1);
  }

  if(cmdline.isset("version"))
  {
    std::cout << LOOPFROG_VERSION << std::endl;
    return 1;
  }
  
  register_languages();
  set_options(cmdline);  

  stream_message_handlert mh(std::cout);  
  set_message_handler(mh);

  int verbosity=6;
  if(cmdline.isset("v"))
  {
    verbosity=atoi(cmdline.getval("v"));
    set_verbosity(verbosity);
  }

  if(cmdline.args.size()==0)
  {
    error("Please provide an input file.");
    return 1;
  }
  else if (cmdline.args.size()>1)
  {
    error("Multiple input files not supported.");
    return 1;
  }

  std::ifstream infile(cmdline.args[0].c_str());
  if (!infile)
  {
    error(std::string("Error opening file `")+cmdline.args[0]+"'.");
    return 1;
  }

  std::string stats_dir;
  if(cmdline.isset("save-stats") ||
     cmdline.isset("save-claims") ||
     cmdline.isset("save-loops"))
  {
    stats_dir = cmdline.args[0] + "_data/";
    #ifndef _WIN32
      mkdir(stats_dir.c_str(), S_IRWXU | S_IRGRP | S_IROTH);
    #else
      mkdir(stats_dir.c_str());
    #endif
  }

  if(cmdline.isset("save-stats"))
  {
    std::string fn=cmdline.args[0]+".lfstat";
    statfile.open(fn.c_str(), std::ios_base::app);
    statfile << cmdline.args[0] << ";";
    statfile.flush();
  }

  if(cmdline.isset("save-summaries"))
  {
    // clean those files
    std::ofstream f("summaries_imprecise"); f.close();
    std::ofstream g("summaries_precise"); g.close();
  }

  // Stage 1: Load file
  goto_functionst goto_functions;
  namespacet ns(context);
  fine_timet before, after;

  status(std::string("#1: Loading `")+cmdline.args[0]+"' ...");
  before=current_time();
  if(read_goto_binary(cmdline.args[0], context, goto_functions, mh))
  {
    error(std::string("Error reading file `")+cmdline.args[0]+"'.");
    return 1;
  }
  after=current_time();
  status(std::string("    LOAD Time: ") + time2string(after-before) + " sec.");
  unsigned long mem = report_mem();
  unsigned inst = count(goto_functions);
  
  if(cmdline.isset("save-stats"))
  {
    statfile << "LOAD;" << time2string(after-before) << ";" << mem << ";" <<
      inst << ";";
    statfile.flush();
  }

  if (cmdline.isset("show-symbol-table"))
  {
    show_symbol_table();
    return true;
  }

  if (cmdline.isset("show-program"))
  {
    goto_functions.output(ns, std::cout);
    return true;
  }

  if(cmdline.isset("save-program"))
  {
    std::ofstream f("goto_program");
    goto_functions.output(ns, f);
    f.close();
  }

  // Stage 2: Loop transformations
  status("#2: Transforming Loops...");
  before=current_time();
  transform_loops(goto_functions, context, mh);
  after=current_time();
  status(std::string("    TRANS Time: ") + time2string(after-before) + " sec.");
  mem = report_mem();
  inst = count(goto_functions);

  if(cmdline.isset("save-stats"))
  {
    statfile << "TRANS;" << time2string(after-before) << ";" << mem << ";" <<
      inst << ";";
    statfile.flush();
  }

  if(cmdline.isset("show-transformed-program"))
  {
    goto_functions.output(ns, std::cout);
    return true;
  }

  if(cmdline.isset("save-transformed-program"))
  {
    std::ofstream f((stats_dir+"goto_program_trans").c_str());
    goto_functions.output(ns, f);
    f.close();
  }

  // Stage 3: Inline marked functions
  status(std::string("#3: Partial Inlining ..."));
  unsigned limit = 10;
  if(cmdline.isset("inlining-limit"))
    limit = atoi(cmdline.getval("inlining-limit"));
  before=current_time();
  goto_partial_inline(goto_functions, ns, mh, limit);
  after=current_time();
  status(std::string("    INL Time: ") + time2string(after-before) + " sec.");
  mem = report_mem();
  inst = count(goto_functions);

  if(cmdline.isset("save-stats"))
  {
    statfile << "INL;" << time2string(after-before) << ";" << mem << ";" <<
      inst << ";";
    statfile.flush();
  }

  if(cmdline.isset("show-inlined-program"))
  {
    goto_functions.output(ns, std::cout);
    return true;
  }

  if(cmdline.isset("save-inlined-program"))
  {
    std::ofstream f((stats_dir+"goto_program_inlined").c_str());
    goto_functions.output(ns, f);
    f.close();
  }

  // Stage 4: Function pointer removal
  status("#4: Removing function pointers...");
  before=current_time();
//  unsigned max_it;
  remove_function_pointers(ns, goto_functions);
  remove_unused_functions(goto_functions, get_message_handler());
  after=current_time();
//  status(std::string("    Max. Iterations: ") + i2string(max_it));
  status(std::string("    RFP Time: ") + time2string(after-before) + " sec.");
  mem=report_mem();
  inst=count(goto_functions);

  if(cmdline.isset("save-stats"))
  {
    statfile << "RFP;" << time2string(after-before) << ";" << mem << ";" << inst
      << ";" ; // << i2string(max_it) << ";";
    statfile.flush();
  }

  if(cmdline.isset("show-fpfreed-program"))
  {
    goto_functions.output(ns, std::cout);
    return true;
  }

  if(cmdline.isset("save-fpfreed-program"))
  {
    std::ofstream f((stats_dir+"goto_program_fpfreed").c_str());
    goto_functions.output(ns, f);
    f.close();
  }

  // Stage 5: String Instrumentation
  status("#5: String instrumentation...");
  before=current_time();
  string_instrumentation(context, mh, goto_functions);
  after=current_time();
  status(std::string("    STRINS Time: ") + time2string(after-before) + " sec.");
  mem=report_mem();
  inst=count(goto_functions);

  if(cmdline.isset("save-stats"))
  {
    statfile << "STRINS;" << time2string(after-before) << ";" << mem << ";" <<
    inst << ";";
    statfile.flush();
  }

  if(cmdline.isset("show-instrumented-program"))
  {
    Forall_goto_functions(it, goto_functions)
      it->second.body.update();
    goto_functions.output(ns, std::cout);
    return true;
  }

  if(cmdline.isset("save-instrumented-program"))
  {
    std::ofstream f((stats_dir+"goto_program_instrumented").c_str());
    goto_functions.output(ns, f);
    f.close();
  }

  // Stage 6: Add generic claims
  status("#6: Adding generic claims...");
  before=current_time();
  goto_check(ns, options, goto_functions);
  after=current_time();
  mem=report_mem();
  inst=count(goto_functions);
  status(std::string("    AGC Time: ") + time2string(after-before) + " sec.");

  if(cmdline.isset("save-stats"))
  {
    statfile << "GCL;" << time2string(after-before) << ";" << mem << ";" <<
      inst << ";";
    statfile.flush();
  }

  if(cmdline.isset("show-claimed-program"))
  {
    goto_functions.output(ns, std::cout);
    return true;
  }

  if(cmdline.isset("save-claimed-program"))
  {
    std::ofstream f((stats_dir+"goto_program_claimed").c_str());
    goto_functions.output(ns, f);
    f.close();
  }

  Forall_goto_functions(it, goto_functions)
  {
    it->second.body.update();

    // HACKFIX: reset function information.
    Forall_goto_program_instructions(i_it, it->second.body)
      i_it->function = it->first;
  }

  // Stage 7: String abstraction
  status("#7: String abstraction...");
  before=current_time();
  string_abstraction(context, mh, goto_functions);
  after=current_time();
  status(std::string("    STRABS Time: ") + time2string(after-before));
  mem=report_mem();
  inst=count(goto_functions);

  if(cmdline.isset("save-stats"))
  {
    statfile << "STRABS;" << time2string(after-before) << ";" << mem << ";" <<
    inst << ";";
    statfile.flush();
  }

  if(cmdline.isset("show-abstracted-program"))
  {
    Forall_goto_functions(it, goto_functions)
      it->second.body.update();
    goto_functions.output(ns, std::cout);
    return true;
  }

  if(cmdline.isset("save-abstracted-program"))
  {
    std::ofstream f((stats_dir+"goto_program_abstracted").c_str());
    goto_functions.output(ns, f);
    f.close();
  }

  // Stage 8: Pointer Analysis
  status("#8: Value set propagation...");
  before=current_time();
  value_set_analysis_fit pointer_analysis(ns);
  pointer_analysis(goto_functions);
  after=current_time();
  status(std::string("    VSP Time: ") + time2string(after-before) + " sec.");
  mem=report_mem();
  inst=count(goto_functions);

  if(cmdline.isset("save-stats"))
  {
    statfile << "VSP;" << time2string(after-before) << ";" << mem << ";" <<
      inst << ";";
    statfile.flush();
  }

  if(cmdline.isset("show-value-sets"))
  {
    forall_goto_functions(it, goto_functions)
    {
      std::cout << "////" << std::endl;
      std::cout << "//// Function: " << it->first << std::endl;
      std::cout << "////" << std::endl;
      std::cout << std::endl;

      pointer_analysis.output(it->second.body, std::cout);
      std::cout << std::endl;
    }
    return true;
  }

  unsigned total=0;
  for (std::map<goto_programt::const_targett, unsigned>::const_iterator it =
        pointer_analysis.statistics.begin();
       it!=pointer_analysis.statistics.end();
       it++)
    if (it->second>total) total=it->second;

  status(std::string("    Max. Iterations: ") + integer2string(total));
  if(cmdline.isset("save-stats"))
  {
    statfile << integer2string(total) << ";";
    statfile.flush();
  }

  value_set_alloc_adaptort adaptor(context, pointer_analysis);

  // Stage 9: Dereference
  status("#9: Pointer dereferencing...");
  before=current_time();
  replace_malloc( context, goto_functions, adaptor );
  Forall_goto_functions(it, goto_functions)
    remove_pointers( it->second.body, context, options, adaptor );
  after=current_time();
  status(std::string("    DEREF Time: ") + time2string(after-before));
  mem=report_mem();
  inst=count(goto_functions);

  if(cmdline.isset("save-stats"))
  {
    statfile << "DEREF;" << time2string(after-before) << ";" << mem << ";" <<
      inst << ";";
    statfile.flush();
  }

  if(cmdline.isset("show-dereferenced-program"))
  {
    goto_functions.output(ns, std::cout);
    return true;
  }

  if(cmdline.isset("save-dereferenced-program"))
  {
    std::ofstream f((stats_dir+"goto_program_dereferenced").c_str());
    goto_functions.output(ns, f);
    f.close();
  }

  if (cmdline.isset("check-by-invariant-propagation"))
  {
    if(check_invariant_propagation(ns, adaptor, goto_functions))
      return 1;
  }
  else
  {
    if(check_loop_summarization(ns, adaptor, goto_functions, stats_dir))
      return 1;
  }

  status("#X: Done.");

  return 0;
}

/*******************************************************************\
  
 Function: loopfrog_parseoptionst::help

 Inputs:

 Outputs:

 Purpose: display command line help

 \*******************************************************************/

void loopfrog_parseoptionst::help()
{
  std::cout <<"\n"
    "* * *                LOOPFROG "LOOPFROG_VERSION
  " - Copyright (C) 2008               * * *\n"
  "          Daniel Kroening, Natasha Sharygina, Aliaksei Tsitovich,\n"
  "                Stefano Tonetta & Christoph M. Wintersteiger\n"
  "\n"
  "Usage:                         Purpose:\n"
  "\n"
  " loopfrog [-?] [-h] [--help]   show help\n"
  " loopfrog [options] <file>     run on goto-binary `file'\n"
  "\nDisplay options:\n"
  "--version                      show version information\n"
  "--show-symbol-table            show symbol table\n"
  "--show-program                 show goto program (as loaded)\n"
  "--show-*-program               show intermediate program, where\n"
  "                               * is one of transformed, inlined,\n"
  "                               fpfreed, instrumented, claimed,\n"
  "                               abstracted, dereferenced, leaping\n"
  "--save-*-program               like --show-*-program, but save the\n"
  "                               program to goto_program_*\n"
  "--no-progress                  turn off progress display\n"
  "\nSummarization options:\n"
  "--save-summaries               save loop summaries to summaries_*\n"
  "--save-loops                   save summarization info in `file'_data/*\n"
  "\nProof Engine options:\n"
  "--show-claims                  output the claims list\n"
  "--show-pass                    report passed claims\n"
  "--suppress-fail                don't report failed claims\n"
  "--save-claims                  save claim info in `file'_data/claim*\n"
  "--bounds-check                 add array bounds checks\n"
  "--pointer-check                add pointer checks\n"
  "--assertions                   add user supplied assertions\n"
  "--claim <int>                  check a specific claim\n"
  "--testclaim <label>            check a labelled claim\n"
  "--ag-reasoning                 enable assume-guarantee reasoning\n"
  "--termination                  enable checking of loops for termination during summarization\n"
  "--no-claim-check               disable assertion check after summarization\n"
  "\nInvariants settings\n"
  "--no-invariants                disable all invariant checks\n"
  "\nState invariants:\n"
  "--zt                           enable the zero-termination domain (default)\n"
  "--ib                           enable the iterator bounds domain (default)\n"
  "--i2                           enable the iterator is positive domain (default)\n"
  "--sb                           enable the strong iterator bounds domain\n"
  "--sl                           enable the constant string length domain\n"
  "--dl                           enable the decreasing string length domain\n"
  "--np                           enable the null pointer domain (default)\n"
  "--ct                           enable the constant string tracker domain\n"
  "--poff                         enable the pointer offset domain\n"
  "--pobj                         enable the pointer object domain\n"
  "--eq                           enable the equality domain\n"
  "--neq                          enable the != domain\n"
  "--ineq                         enable the <= and >= domain\n"
  "\nTransition Invariants\n"
  "--ti1                          enable the \"i'>/<i\" domain for numeric variables (default for --termination)\n"
  "--ti2                          enable the \"x'>/<x\" domain dor all variables\n"
  "--ti3                          enable the \"a'+b'>/<a+b\" (sum) domain for numeric variables\n"
  "--ti4                          enable the \"max(a',b')>/<max(a,b)\" (max or min) domain for numeric variables\n"
  "--ti5                          enable the \"(a'>a and b'=b) or...\" domain\n"
  "--st1                          enable the \"i'>/<i\" domain with premises i>=0 or i<MAX(i) or i> MIN(i)\n"
  "\n";
//  "--st2                          enable the \"(a'>a and b'=b) or...\" domain with premises a>=0 & b>=0\n"
//  "--interactive                  enable user input of invariant candidates\n"

}

/*******************************************************************\
  
 Function: 

 Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

unsigned loopfrog_parseoptionst::count(const goto_functionst &goto_functions) const
{
  unsigned long c=0;
  for(goto_functionst::function_mapt::const_iterator it =
        goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    c += it->second.body.instructions.size();
  std::cout << "    Instruction count: " << c << std::endl;
  return c;
}

/*******************************************************************\
  
 Function: 

 Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

unsigned loopfrog_parseoptionst::count(
  const goto_functionst &goto_functions,
  const loopstoret &imprecise_summaries,
  const loopstoret &precise_summaries,
  unsigned add) const
{
  unsigned long c=0;

  for(goto_functionst::function_mapt::const_iterator it =
        goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    c += it->second.body.instructions.size();

  for(loopstoret::const_iterator it=imprecise_summaries.begin();
      it!=imprecise_summaries.end();
      it++)
    c+=it->second.instructions.size();

  for(loopstoret::const_iterator it=precise_summaries.begin();
      it!=precise_summaries.end();
      it++)
    c+=it->second.instructions.size();

  c+=add;

  std::cout << "    Instruction count: " << c << std::endl;

  return c;
}

/*******************************************************************\
  
 Function: 

 Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

unsigned loopfrog_parseoptionst::count(const goto_programt &goto_program) const
{
  std::cout << "    Instruction count: " << goto_program.instructions.size()
    << std::endl;
  return goto_program.instructions.size();
}

/*******************************************************************\
  
 Function: 

 Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

unsigned long loopfrog_parseoptionst::report_mem(void) const
{
  unsigned long l = current_memory();
  unsigned long mbs = l / 1048576;

  std::cout << "    MEM: "
  << mbs << " MB " <<
  "(" << l << " Bytes)." << std::endl;

  return mbs;
}

/*******************************************************************\
  
 Function: 

 Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

unsigned long loopfrog_parseoptionst::report_max_mem(unsigned long mem) const
{
  unsigned long mbs = mem / 1048576;

  std::cout << "    MEM: "
  << mbs << " MB " <<
  "(" << mem << " Bytes)." << std::endl;

  return mbs;
}

/*******************************************************************\
  
 Function: 

 Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool loopfrog_parseoptionst::check_invariant_propagation(
  namespacet &ns,
  value_set_alloc_adaptort &adaptor,
  goto_functionst &goto_functions)
{
  unsigned long mem;
  unsigned inst;
  fine_timet before, after;
  
  status("#10: Invariant Propagation...");
  before = current_time();

  invariant_propagation_adaptort invariant_propagation(ns, adaptor);
  invariant_propagation(goto_functions);
  after = current_time();
  status(std::string("    IP time: ") + time2string(after - before));
  mem = report_mem();
  inst=count(goto_functions);
    
  if(cmdline.isset("save-stats"))
  {
    statfile << "IP;" << time2string(after-before) << ";" << mem << ";" <<
      inst << ";0;0;0;";
    statfile.flush();
  }
  
  before = current_time();  
  status("#11: Checking claims...");
  claim_statst stats = check_claims_using_domain(ns, goto_functions,
                                                 invariant_propagation, true);
  after = current_time();
  
  if(!cmdline.isset("no-progress")) std::cout << "\r";
  status(std::string("    PASS: ")+i2string(stats.claims_passed)+
                        " FAIL: "+i2string(stats.claims_failed) + " ");
  status(std::string("    CC Time: ") + time2string(after-before) + " sec.");
  status(std::string("    Time spent in SAT SOLVER: ") +
           time2string(global_satsolver_time) + " sec.");
  status(std::string("    Time spent in SAT CONVERSION: ") +
             time2string(global_sat_conversion_time) + " sec.");
  mem = report_mem();

  if (cmdline.isset("save-stats"))
  {
    statfile << "CC;" << time2string(after-before) << ";" << mem << ";" <<
      inst << ";CLAIMS;" << stats.claims_passed << ";" <<
      stats.claims_failed <<
      ";SAT;" << time2string(global_satsolver_time) <<
      ";SCONV;" << time2string(global_sat_conversion_time) << ";";
    statfile.close();
  }
  
  return 0;
}

/*******************************************************************\
  
 Function: 

 Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool loopfrog_parseoptionst::check_loop_summarization(
  namespacet &ns,
  value_set_alloc_adaptort &adaptor,
  goto_functionst &goto_functions,
  std::string &stats_dir)
{
  unsigned long mem;
  unsigned inst;
  fine_timet before, after;
  
  claim_mapt claim_map;
  claim_numberst claim_numbers;
  
  // we don't create copies...
  goto_functionst &leaping_functions = goto_functions;
  
  loop_summarizer_statst sumstats;
  
  // Stage 10: The loop summarization
  status("#10: Loop Summarization...");
  
  loopstoret imprecise_loops;
  loopstoret precise_loops;


  string_summarizationt strsum( context, leaping_functions, imprecise_loops, precise_loops,adaptor, stats_dir, options );

  before=current_time();
  sumstats = summarize(goto_functions, context, strsum,
                       imprecise_loops, precise_loops, adaptor,
                       get_message_handler(), cmdline, stats_dir);
  if(!cmdline.isset("no-progress") &&
     !cmdline.isset("no-invariants"))
    strsum.print_statistics(std::cout);
  after=current_time();
  status(std::string("    LS Time: ") + time2string(after-before) + " sec.");
  if(cmdline.isset("no-invariants"))
    mem = report_mem();
  else
    mem=report_max_mem(strsum.max_mem_used);
  inst=count(goto_functions, imprecise_loops, precise_loops, 0);
  
  if(cmdline.isset("save-stats"))
  {
    statfile << "LS;" << time2string(after-before) << ";" << mem << ";" <<
      inst << ";" << strsum.seen_loops << ";" << sumstats.good << ";" <<
      sumstats.bad << ";";
    statfile.flush();
  }
  
  Forall_goto_functions(it, leaping_functions)
  {
    compress_program(it->second.body);
    it->second.body.update();
  }
  
  if (cmdline.isset("show-leaping-program"))
  {
    forall_goto_functions(it, leaping_functions)
    {
      std::cout << it->first << ": " << std::endl;
      std::cout << "---------------" << std::endl;
      it->second.body.output(ns, "", std::cout);
    }
  
    return true;
  }
  
  if (cmdline.isset("save-leaping-program"))
  {
    std::ofstream f((stats_dir+"goto_program_leaping").c_str());
    forall_goto_functions(it, leaping_functions)
    {
      f << it->first << ": " << std::endl;
      f << "---------------" << std::endl;
      it->second.body.output(ns, "", f);
    }
    f.close();
  }
  
  get_claims(leaping_functions, precise_loops, claim_map, claim_numbers);
  
  if(cmdline.isset("show-claims"))
  {
    show_claims(ns, claim_map, claim_numbers);    
    return true;
  }

  if(options.get_bool_option("no-claim-check"))
    return true;

  // Stage 10: Finally checking some claims.
  status("#11: Checking claims in leaping program...");
  
  unsigned claim_nr=0;
  
  if(cmdline.isset("testclaim"))
  {
    claim_nr=find_marked_claim(leaping_functions,                               
                               precise_loops,
                               cmdline.getval("testclaim"),
                               claim_numbers);
    if(claim_nr==(unsigned) -1)
    {
      error("Testclaim not found.");
      return 1;
    }
  }
  else if(cmdline.isset("claim"))
    claim_nr=atoi(cmdline.getval("claim"));
  
  before=current_time();
  claim_statst stats = check_claims(ns,
                                    leaping_functions.function_map["main"].body,
                                    leaping_functions,
                                    imprecise_loops,
                                    precise_loops,
                                    stats_dir,
                                    claim_map,
                                    claim_numbers,
                                    claim_nr,
                                    cmdline.isset("show-pass"),
                                    !cmdline.isset("suppress-fail"),
                                    !cmdline.isset("no-progress"),
                                    cmdline.isset("save-claims"),
                                    cmdline.isset("ag-reasoning"),
                                    cmdline.isset("check-by-invariant-propagation"),
                                    cmdline.isset("use-smt"));
  after=current_time();
  if(!cmdline.isset("no-progress")) std::cout << "\r";
  status(std::string("    PASS: ")+i2string(stats.claims_passed +
                                            sumstats.good)+
                        " FAIL: "+i2string(stats.claims_failed) + " ");
  status(std::string("    CC Time: ") + time2string(after-before) + " sec.");
  status(std::string("    Time spent in SAT SOLVER: ") +
           time2string(global_satsolver_time) + " sec.");
  status(std::string("    Time spent in SAT CONVERSION: ") +
             time2string(global_sat_conversion_time) + " sec.");
  mem=report_max_mem(stats.max_mem_used);
  inst=count(goto_functions, imprecise_loops,
             precise_loops, stats.max_instruction_count);
  
  if(cmdline.isset("save-stats"))
  {
    statfile << "CC;" << time2string(after-before) << ";" << mem << ";" <<
      inst << ";CLAIMS;" << stats.claims_passed << ";" <<
      stats.claims_failed <<
      ";SAT;" << time2string(global_satsolver_time) <<
      ";SCONV;" << time2string(global_sat_conversion_time) << ";";
    statfile.close();
  }
  
  return 0;
}

/*******************************************************************\
  
 Function: 

 Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void loopfrog_parseoptionst::set_options(const cmdlinet &cmdline)
{
  options.set_option("bounds-check", cmdline.isset("bounds-check"));
  options.set_option("pointer-check", cmdline.isset("pointer-check"));
  options.set_option("assertions", cmdline.isset("assertions"));

  options.set_option("incremental", cmdline.isset("incremental"));
  options.set_option("interactive", cmdline.isset("interactive"));

  options.set_option("zt", cmdline.isset("zt"));
  options.set_option("ib", cmdline.isset("ib"));
  options.set_option("i2", cmdline.isset("i2"));
  options.set_option("sb", cmdline.isset("sb"));
  options.set_option("sl", cmdline.isset("sl"));
  options.set_option("dl", cmdline.isset("dl"));
  options.set_option("np", cmdline.isset("np"));
  options.set_option("ct", cmdline.isset("ct"));
  options.set_option("poff", cmdline.isset("poff"));
  options.set_option("pobj", cmdline.isset("pobj"));
  options.set_option("eq", cmdline.isset("eq"));
  options.set_option("neq", cmdline.isset("neq"));
  options.set_option("ineq", cmdline.isset("ineq"));

  options.set_option("termination", cmdline.isset("termination"));
  options.set_option("no-claim-check", cmdline.isset("no-claim-check"));
  options.set_option("ti1", cmdline.isset("ti1"));
  options.set_option("ti2", cmdline.isset("ti2"));
  options.set_option("ti3", cmdline.isset("ti3"));
  options.set_option("ti4", cmdline.isset("ti4"));
  options.set_option("ti5", cmdline.isset("ti5"));
  options.set_option("st1", cmdline.isset("st1"));
  options.set_option("st2", cmdline.isset("st2"));

  if(cmdline.isset("ti2"))
      options.set_option("ti1", false); //redundunt

  if(cmdline.isset("termination"))
  {
      options.set_option("no-claim-check", true); //redundunt
      if(!(cmdline.isset("ti1") ||
       cmdline.isset("ti2") ||
       cmdline.isset("ti3") ||
       cmdline.isset("ti4") ||
       cmdline.isset("ti5") ||
       cmdline.isset("st1") ||
       cmdline.isset("st2")))
  	  {
      	options.set_option("ti1", true); //set default termination engine
  	  }
  }
  if(!(cmdline.isset("zt") ||
       cmdline.isset("ib") ||
       cmdline.isset("i2") ||
       cmdline.isset("sb") ||
       cmdline.isset("sl") ||
       cmdline.isset("dl") ||
       cmdline.isset("np") ||
       cmdline.isset("ct") ||
       cmdline.isset("poff") ||
       cmdline.isset("pobj") ||
       cmdline.isset("eq") ||
       cmdline.isset("neq") ||
       cmdline.isset("ineq")||
       cmdline.isset("termination")||
       cmdline.isset("ti1")||
       cmdline.isset("ti2")||
       cmdline.isset("ti3")||
       cmdline.isset("ti4")||
       cmdline.isset("ti5")||
       cmdline.isset("st1")||
       cmdline.isset("st2")))
  {
    // if nothing was chosen, add defaults
    options.set_option("zt", true);
    options.set_option("ib", true);
    options.set_option("i2", true);
    options.set_option("np", true);
  }

  options.set_option("no-invariants", cmdline.isset("no-invariants"));
  options.set_option("save-loops", cmdline.isset("save-loops"));
  options.set_option("use-smt", cmdline.isset("use-smt"));
}
