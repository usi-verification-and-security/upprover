/*******************************************************************\
  
Module: Prepare a C program for use by CEGAR

Author: Daniel Kroening
        Karen Yorav

Date: June 2003
 
\*******************************************************************/

#include <fstream>
#include <memory>

#include <expr_util.h>
#include <str_getline.h>
#include <get_module.h>
#include <i2string.h>
#include <xml.h>
#include <xml_irep.h>

#include <ansi-c/ansi_c_language.h>

#include <goto-programs/show_claims.h>
#include <goto-programs/set_claims.h>
#include <goto-programs/goto_check.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/slicer.h>
#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_function_pointers.h>
#include <goto-programs/add_race_assertions.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/string_instrumentation.h>
#include <goto-programs/string_abstraction.h>
#include <goto-programs/loop_numbers.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/invariant_propagation.h>

#include <langapi/language_util.h>
#include <langapi/mode.h>
#include <langapi/languages.h>

#include <pointer-analysis/goto_program_dereference.h>
#include <pointer-analysis/add_failed_symbols.h>
#include <pointer-analysis/value_set_analysis.h>
#include <pointer-analysis/show_value_sets.h>

#include "../version.h"
#include "prepare.h"
#include "prepare_functions.h"

#define MAX_BLOCK_SIZE 1

/*******************************************************************\

Function: preparet::preparet

  Inputs:

 Outputs:

 Purpose: convert input program into goto program

\*******************************************************************/

preparet::preparet(
  const cmdlinet &_cmdline,
  const optionst &_options,
  contextt &_shadow_context): 
  language_uit("SATABS " SATABS_VERSION, _cmdline),
  ns(context, _shadow_context),
  shadow_context(_shadow_context),
  cmdline(_cmdline),
  options(_options)
{
}

/*******************************************************************\

Function: preparet::doit

  Inputs:

 Outputs:

 Purpose: convert input program into goto program

\*******************************************************************/

bool preparet::doit()
{
  register_languages();
  
  try
  {
    // do we have a goto binary?
    if(cmdline.args.size()==1 &&
       is_goto_binary(cmdline.args[0]))
    {
      status("Reading GOTO program from file");

      if(read_goto_binary(cmdline.args[0],
           context, goto_functions,
           get_message_handler()))
        return true;
        
      config.ansi_c.set_from_context(context);
    }
    else
    {
      //
      // parsing
      //
       
      if(parse()) return true;
       
      //
      // type checking
      //
       
      if(typecheck()) return true;
       
      //
      // final adjustments
      //
       
      if(final()) return true;
    }
   
    if(get_sync_modules())
      return true;
    
    if(get_async_modules())
      return true;
      
    // we no longer need any parse trees or language files
    clear_parse();
     
    if(cmdline.isset("show-claims"))
    {
      show_claims(ns, get_ui(), goto_functions);
      return true;
    }

    // get the user provided predicates

    if(cmdline.isset("predicates"))
      get_predicates();
  }

  catch(const char *e)
  {
    error(e);
    return true;
  }

  catch(const std::string e)
  {
    error(e);
    return true;
  }
  
  catch(int)
  {
    return true;
  }
  
  return false;
}

/*******************************************************************\

Function: preparet::get_predicates

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void preparet::get_predicates()
{
  std::ifstream infile(cmdline.getval("predicates"));

  if(!infile)
    throw std::string("failed to open ")+cmdline.getval("predicates");

  // we only do C expressions right now

  languaget *l=new ansi_c_languaget;

  // use auto_ptr because of the exceptions
  std::auto_ptr<languaget> language(l);

  std::string line;

  while(infile)
  {
    str_getline(infile, line);

    if(line!="" && line[0]!='#' &&
       std::string(line, 0, 2)!="//")
    {
      exprt expr;

      if(language->to_expr(line, "", expr, get_message_handler(), ns))
        throw "failed to parse `"+line+"'";

      if(expr.type().id()!="bool")
      {
        std::string type_string;
        language->from_type(expr.type(), type_string, ns);
        throw "expected boolean expression as predicate, but got `"+type_string+"'";
      }

      user_provided_predicates.push_back(expr);
    }
  }
}

/*******************************************************************\

Function: preparet::get_sync_modules

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool preparet::get_sync_modules()
{
  return false;
}

/*******************************************************************\

Function: preparet::get_async_modules

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool preparet::get_async_modules()
{
  if(goto_functions.function_map.empty())
  {
    // see if we have a "main"

    if(context.symbols.find("main")==context.symbols.end())
    {
      error("failed to find entry point -- please provide a model");
      return true;
    }

    status("Generating GOTO Program");

    goto_convert(
      context,
      options,
      goto_functions,
      get_message_handler());
  }
    
  if(cmdline.isset("show-goto-functions"))
  {
    goto_functions.output(ns, std::cout);
    return true;
  }
  
  unsigned functions=goto_functions.function_map.size();
  unsigned instructions=0;
  forall_goto_functions(it, goto_functions)
    instructions+=it->second.body.instructions.size();
  
  status(i2string(functions)+" functions, "+
         i2string(instructions)+" instructions.");
  
  if(cmdline.isset("string-abstraction"))
    string_instrumentation(
      context, get_message_handler(), goto_functions);

  status("Removing function pointers");
  remove_function_pointers(ns, goto_functions);

  status("Removing unused functions");
  remove_unused_functions(
    goto_functions, get_message_handler());

  if(cmdline.isset("full-inlining"))
  {
    status("Full inlining");

    goto_inline(
      goto_functions,
      ns,
      get_message_handler());
  }
  else
  {
    // partially inline functions
    status("Partial inlining");

    goto_partial_inline(
      goto_functions,
      ns,
      get_message_handler());
  
    // we do this again, to remove all the functions that are inlined now
    remove_unused_functions(
      goto_functions, get_message_handler());

    status("Adjusting functions");
    prepare_functions(
      context,
      goto_functions,
      get_message_handler());

    // show it?
    if(cmdline.isset("show-adjusted-functions"))
    {
      goto_functions.output(ns, std::cout);
      return true;
    }
  }
  
  // add loop ids
  goto_functions.compute_loop_numbers();

  // show it?
  if(cmdline.isset("show-loops"))
  {
    show_loop_numbers(get_ui(), goto_functions);
    return true;
  }

  add_failed_symbols(context);

  // add generic checks
  goto_check(ns, options, goto_functions);

  if(cmdline.isset("string-abstraction"))
  {
    status("String Abstraction");
    string_abstraction(
      context,
      get_message_handler(),
      goto_functions);
  }  
  
  goto_functions.compute_location_numbers();

  if(cmdline.isset("pointer-check") ||
     cmdline.isset("show-value-sets") ||
     cmdline.isset("data-race-check"))
  {
    status("Pointer Analysis");
    value_set_analysist value_set_analysis(ns);
    value_set_analysis(goto_functions);

    // show it?
    if(cmdline.isset("show-value-sets"))
    {
      show_value_sets(get_ui(), goto_functions, value_set_analysis);
      return true;
    }

    if(cmdline.isset("pointer-check"))
    {
      status("Adding Pointer Checks");

      // add pointer checks
      pointer_checks(
        goto_functions, ns, options, value_set_analysis);
    }

    if(cmdline.isset("data-race-check"))
    {
      status("Adding Data Race Checks");

      add_race_assertions(
        value_set_analysis,
        context,
        goto_functions);

      value_set_analysis.
        update(goto_functions);
    }
  }
  
  goto_functions.compute_location_numbers();

  #if 0  
  // do invariant propagation
  if(!cmdline.isset("no-invariant-sets"))
  {
    status("Invariant Propagation");
    invariant_propagation(
      goto_functions);
  }
  else
    invariant_propagation.initialize(
      goto_functions);

  if(cmdline.isset("show-invariant-sets"))
  {
    invariant_propagation.output(
      goto_functions, std::cout);
    return true;
  }

  // simplify
  if(!cmdline.isset("no-invariant-sets"))
    invariant_propagation.simplify(
      goto_functions);
  #endif

  // set claim
  if(cmdline.isset("claim"))
    set_claims(
      goto_functions,
      cmdline.get_values("claim"));
      
  // slice
  if(!cmdline.isset("no-slicing"))
    slicer(goto_functions);

  // show it?

  if(cmdline.isset("show-final-program"))
  {
    goto_functions.output(ns, std::cout);
    return true;
  }

  return false;
}

