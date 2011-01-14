/*******************************************************************\

Module: Loop Summarization (without Inlining)

Author: CM Wintersteiger

\*******************************************************************/

#include <sys/stat.h>
#ifdef _WIN32
#include <io.h>
#endif

#include <base_type.h>
#include <i2string.h>
#include <ansi-c/expr2c.h>

#include "pointer_expr.h"
#include "loop_summarizer.h"
#include "summarization.h"
#include "program_compression.h"
#include "local_slicer.h"
#include "symex_assertion.h"
#include "leaping_goto_program.h"
#include "localized_inlining.h"
#include "call_stack.h"

/*******************************************************************\

Function: summarize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

loop_summarizer_statst summarize(
  goto_functionst &goto_functions,
  contextt &context,
  summarizationt &sum,
  loopstoret &imprecise_loops,
  loopstoret &precise_loops,
  value_setst &value_sets,
  message_handlert &message_handler,
  cmdlinet &cmdline,
  const std::string &stats_dir)
{
  loop_summarizert summarizer(context, sum, goto_functions,
                              imprecise_loops, precise_loops,
                              value_sets, stats_dir,
                              message_handler, cmdline);

  goto_functionst::function_mapt::iterator main_it =
    goto_functions.function_map.find("main");
  if (main_it==goto_functions.function_map.end())
  {
    throw "main could not be found";
  }
  goto_programt &main = main_it->second.body;

  summarizer.summarize("main", main, goto_functions);

  loop_summarizer_statst res;
  return res;
}

/*******************************************************************\

Function: loop_summarizert::summarize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void loop_summarizert::summarize(
  const irep_idt &name,
  goto_programt &program,
  goto_functionst &goto_functions)
{
  if(!cmdline.isset("no-progress"))
    std::cout << "\r    Collecting loop stats..."; std::cout.flush();

  total_loops=fix_location_numbering(goto_functions);

	if(!cmdline.isset("no-progress"))
	  std::cout << "\r                                     "; std::cout.flush();

  summarize_rec(name, program);
  fix_location_numbering(program);

  if(!cmdline.isset("no-progress"))
    std::cout << "\r";
}

/*******************************************************************\

Function: loop_summarizert::summarize_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void loop_summarizert::summarize_rec(
  const irep_idt &name,
  goto_programt &program)
{
  #if 0
  std::cout << "SUMMARIZE_REC: " << name << std::endl;
  #endif

  recursion_sett::iterator rec_it = recursion_set.insert(name).first;

  Forall_goto_program_instructions(it, program)
  {
    if (it->is_function_call())
    {
      const code_function_callt &call =
        to_code_function_call(to_code(it->code));

      if(call.function().id()=="symbol")
      {
        #if 0
        std::cout << "FUNCTION SUMMARY FOR: " <<
          call.function().get("identifier") << std::endl;
        #endif

        const irep_idt call_name = call.function().get("identifier");

        // check for recursion problems
        if(recursion_set.find(call_name)!=recursion_set.end())
        {
          err_location(call.location());
          warning("ignoring recursion");
          it->type = SKIP; // kill the call.
        }
        else if(functions_summarized.find(call_name)==
                functions_summarized.end())
          summarize_rec(call_name, goto_functions.function_map[call_name].body);
      }
      else if(call.function().id()=="builtin-function")
      {
        // ignore
      }
      else
      {
        str << "Non-Symbol function call: " << call.function();
        error(str.str());
        throw 0;
      }
    }
    else if (it->is_backwards_goto()) // we need to summarize this loop
    {
      assert(it->targets.size()==1); // we don't handle nondet-gotos for now

      goto_programt::instructionst::iterator next_it = it; next_it++;

      summarize_loop(program, it->targets.front(), it);

      it=--next_it;
    }
    // else: this is something else, just keep the copy.
  }

  recursion_set.erase(rec_it);
  functions_summarized.insert(name);
}


/*******************************************************************\

Function: loop_summarizert::summarize_loop

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void loop_summarizert::summarize_loop(
  goto_programt &goto_program,
  goto_programt::targett begin,
  goto_programt::targett end)
{
  #if 0
  std::cout << "SUMMARIZE_LOOP: " << begin->function << " " <<
    begin->location_number << " to " <<
    end->location_number << std::endl;
  #endif

  #if 0
  std::cout << "SUMMARIZING THIS LOOP: " << std::endl;
  goto_programt::const_targett t_it = begin;
  for( ; t_it!=end; t_it++)
    goto_program.output_instruction(ns, "", std::cout, t_it);
  goto_program.output_instruction(ns, "", std::cout, t_it);
  #endif

  // begin is the loop head,
  // end is the backjump

  #if 0
  // first of all, we run a few debugging tests

  // check for bogus function calls
  for (goto_programt::targett i = begin; i!=end; i++)
  {
    if(i->is_function_call())
    {
      const code_function_callt &code=
        to_code_function_call(to_code(i->code));

      if(code.function().id()=="symbol")
      {
        const irep_idt &c_name = code.function().get("identifier");

        // sanity check, all needed functions should be summarized already
        assert(functions_summarized.find(c_name)!=
               functions_summarized.end());
      }
      else
        assert(code.function().id()=="builtin-function");
    }
    assert (!(i->is_backwards_goto()));
  }
  #endif

  current_loop_nr++;
  if(!cmdline.isset("no-progress"))
  {
    std::cout << "\r    Loop " << current_loop_nr << "/" << total_loops;
    std::cout.flush();
  }

  std::ofstream out;

  if (cmdline.isset("save-loops"))
  {
    std::string dname = stats_dir + "loop_";
    dname += i2string(current_loop_nr);
    #ifndef _WIN32
      mkdir(dname.c_str(), S_IRWXU | S_IRGRP | S_IROTH);
    #else
      mkdir(dname.c_str());
    #endif
    out.open((dname+"/loop").c_str());

    goto_programt::const_targett t_it = begin;
    for( ; t_it!=end; t_it++)
      goto_program.output_instruction(ns, "", out, t_it);
    goto_program.output_instruction(ns, "", out, t_it);

    out << std::endl;
  }

  // immediately kill the backjump
  // [it's only an if(true) anyways]
  end->type=SKIP;
  end->targets.clear();

  // replacement instruction
  goto_programt::instructiont newins;
  newins.make_other();
  codet code("loop-summary");
  code.set("index", current_loop_nr);
  newins.code = code;
  newins.location_number = begin->location_number;
  newins.function = begin->function;
  goto_program.insert_before_swap(begin, newins);
  begin++;

  goto_programt::targett next = end; next++;
  goto_programt summary_program;

  summary_program.instructions.splice(
    summary_program.instructions.end(),
    goto_program.instructions,
    begin, next); // cut it out, including the backjump!  

  // let's be nice to the summarizer and inline the program first
  goto_programt summary_program_inlined;

  goto_inline_localizedt::progresst inlining_progress(summary_program,
                                                      summary_program_inlined,
                                                      false);

  goto_inline_localizedt gil(goto_functions,
                             inlining_progress,
                             imprecise_loops,
                             precise_loops,
                             ns);

  call_stackt stack;
  goto_programt::targett last = summary_program.instructions.end();
  last--;
  gil.goto_inline(stack, last, out);

  if (cmdline.isset("save-loops")) out.close();

  // create those summaries...
  loop_summaryt summary;
  prepare_loop_body(summary_program_inlined);
  prepare_loop_body(summary_program);

  goto_programt::const_targett head = begin;
  summarization.summarize_loop(head,
                               summary_program_inlined,
                               summary);

  create_imprecise_loop_summary(summary);
  create_precise_loop_summary(summary_program, summary);

  #if 0
  summary_program_inlined.compute_targets();
  summary_program_inlined.number_targets();
  std::cout << "Program after summarization" << std::endl;

  forall_goto_program_instructions(it, summary_program_inlined)
    summary_program_inlined.output_instruction(ns, "", std::cout, it);
  #endif

  #if 0
  std::cout << "Loop summarized." << std::endl;
  #endif
}

/*******************************************************************\

Function: loop_summarizert::fix_location_numbering

  Inputs:

 Outputs:

 Purpose: fixes 0-locations by propagating the last seen loc. number,
          also returns the number of loops in the program.

\*******************************************************************/

unsigned loop_summarizert::fix_location_numbering(goto_programt &program) const
{
  unsigned res = 0;

  unsigned last_good_location_number=0;

  Forall_goto_program_instructions(it, program)
  {
    if(it->location_number==0)
      it->location_number=last_good_location_number;
    else
      last_good_location_number=it->location_number;

    if (it->is_backwards_goto())
      res++;
  }

  return res;
}

/*******************************************************************\

Function: loop_summarizert::move_returns

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void loop_summarizert::move_returns(goto_programt &dest)
{
  if(dest.instructions.size()==0) return;

  #if 0
  std::cout << "BEFORE MOVING RETURNS" << std::endl;
  dest.output(ns, "", std::cout);
  std::cout << "---------------------" << std::endl;
  #endif

  assert(dest.instructions.back().type==END_FUNCTION);

  goto_programt::targett eof = dest.instructions.end(); eof--;
  goto_programt::targett last_instruction = eof; last_instruction--;

  assert(eof->is_end_function());

  Forall_goto_program_instructions(it, dest)
  {
    if(it->is_return())
    {
      goto_programt::targett new_return = dest.insert_before(eof);
      new_return->swap(*it);
      new_return->location_number = it->location_number; // preserve alias data
      new_return->function = it->function;

      it->make_goto(new_return);
    }

    if(it==last_instruction) break;
  }

  dest.update();

  #if 0
  std::cout << "AFTER MOVING RETURNS" << std::endl;
  dest.output(ns, "", std::cout);
  #endif
}

/*******************************************************************\

Function: loop_summarizert::fix_location_numbering

  Inputs:

 Outputs:

 Purpose: fixes 0-locations by propagating the last seen loc. number

\*******************************************************************/

unsigned loop_summarizert::fix_location_numbering(
	goto_functionst &functions) const
{
  unsigned res = 0;

  Forall_goto_functions(it, functions)
    res += fix_location_numbering(it->second.body);

  return res;
}

/*******************************************************************\

Function: loop_summarizert::create_imprecise_loop_summary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void loop_summarizert::create_imprecise_loop_summary(
  loop_summaryt &summary) const
{
  goto_programt &summary_program = imprecise_loops[current_loop_nr];

  goto_programt preconditions;
  summary.get_preconditions_program(context, preconditions);
  summary_program.instructions.splice(summary_program.instructions.end(),
                                      preconditions.instructions);

  goto_programt variants;
  summary.get_variants_program(value_sets, variants);
  summary_program.instructions.splice(summary_program.instructions.end(),
                                      variants.instructions);

  goto_programt invariants;
  summary.get_invariants_program(context, invariants);
  summary_program.instructions.splice(summary_program.instructions.end(),
                                      invariants.instructions);

  summary_program.insert_before(summary_program.instructions.end())->type=END_FUNCTION;

  summary_program.update();

  if(cmdline.isset("save-summaries"))
  {
    std::ofstream f("summaries_imprecise", std::ios::app);
    f << "Loop Summary #" << current_loop_nr << std::endl;
    f << "--------------------" << std::endl;
    summary_program.output(ns, "", f);
    f << std::endl;
    f.close();
  }
}

/*******************************************************************\

Function: loop_summarizert::create_precise_loop_summary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void loop_summarizert::create_precise_loop_summary(
  goto_programt &loop_program,
  loop_summaryt &summary)
{
  goto_programt &summary_program = precise_loops[current_loop_nr];
  summary_program.copy_from(loop_program);

  // we don't add the imprecise summary data here!

  goto_programt::targett eof =
    summary_program.insert_before(summary_program.instructions.end());
  eof->type=END_FUNCTION;

  std::list<exprt> exit_guards;

  Forall_goto_program_instructions(it, summary_program)
  {
    switch (it->type)
    {
      case SKIP:
      {
        goto_programt::instructiont::labelst::iterator lit =
          find(it->labels.begin(),
               it->labels.end(),
               irep_idt("DISABLED_ASSERT"));

        if(lit!=it->labels.end())
        {
          it->labels.erase(lit);
          it->type=ASSERT; // reactivated!
        }
        break;
      }
      case ASSUME:
      {
        goto_programt::instructiont::labelst::iterator lit =
          find(it->labels.begin(),
               it->labels.end(),
               irep_idt("DISABLED_GOTO"));

        if(lit!=it->labels.end())
        {
          it->labels.erase(lit);
          it->guard.make_not();
          it->type=GOTO; // reactivated!
          it->targets.clear();
          it->targets.push_back(eof);

          // this is an exit guard!
          exit_guards.push_back(it->guard);
        }
        else
        {
          lit = find(it->labels.begin(), it->labels.end(),
                     irep_idt("DISABLED_RETURN"));

          if(lit!=it->labels.end())
          {
            it->labels.erase(lit);
            it->type=RETURN;
          }
        }
        break;
      }
      default:
      {
        // just keep everything else. is this sound?
        break;
      }
    }
  }

  exprt postcondition;
  if(!exit_guards.empty())
  {
    if(exit_guards.size()==1)
      postcondition=exit_guards.front();
    else
    {
      postcondition=exprt("or", bool_typet());
      for(std::list<exprt>::iterator it=exit_guards.begin();
          it!=exit_guards.end();
          it=exit_guards.erase(it))
      {
        postcondition.move_to_operands(*it);
      }
    }

    if(!postcondition.is_true())
    {
      goto_programt::instructiont newins;
      newins.type=ASSUME;
      newins.guard=postcondition;
      summary_program.insert_before_swap(eof, newins);
    }
  }

  nondet_slicer(summary_program);
  summary_program.update();

  if(cmdline.isset("save-summaries"))
  {
    std::ofstream f("summaries_precise", std::ios::app);
    f << "Loop Summary #" << current_loop_nr << std::endl;
    f << "--------------------" << std::endl;
    summary_program.output(ns, "", f);
    f << std::endl;
    f.close();
  }
}

/*******************************************************************

 Function: loop_summarizert::prepare_loop_body

 Inputs:

 Outputs:

 Purpose: Prepares loop body to be used in symex

 \*******************************************************************/

void loop_summarizert::prepare_loop_body(goto_programt &source)
{
  goto_programt::targett last = --source.instructions.end();

  Forall_goto_program_instructions(it, source)
  {
    switch (it->type)
    {
      case GOTO:
      {
        assert(it->targets.size()==1);

        // if something jumps out of this program, turn it into
        // an assumption; the target is set to the EOF,
        // since we assume that all loop exits point to the
        // instruction after the loop
        if (it->targets.front()->location_number >
            last->location_number)
        {
          it->guard.make_not();
          it->type=ASSUME;
          it->labels.push_back("DISABLED_GOTO");
          it->targets.clear();
        }
        break;
      }
      case RETURN:
      {
        it->type = ASSUME;
        it->guard.make_false();
        it->labels.push_back("DISABLED_RETURN");
        break;
      }
      case ASSERT:
      {
        it->type=SKIP; // keep guard!
        it->labels.push_back("DISABLED_ASSERT");
        break;
      }
      case OTHER:
      {
        codet &code = to_code(it->code);

        if (code.get_statement()=="free")
        {
          code.set_statement("expression");
          it->labels.push_back("DISABLED_FREE");
        }

        break;
      }
      case ASSIGN:
      {
        const codet &code = to_code(it->code);

        if (code.get_statement()=="malloc")
        {
          assert(false); // there shouldn't be any mallocs in this program.
        }

        break;
      }
//      case FUNCTION_CALL:
//      {
//        const code_function_callt &code=
//            to_code_function_call(to_code(it->code));
//
//        if (code.function().id()=="builtin-function")
//          it->make_skip();
//
//        break;
//      }
      default: /*nothing*/
        ;
    }
  }
}

