/*******************************************************************\

Module: Generic Loop Summarization

Author: CM Wintersteiger

\*******************************************************************/

#include <memory>
#include <ansi-c/expr2c.h>
#include <i2string.h>
#include <config.h>

#include <expr_util.h>
#include <str_getline.h>
#include <ansi-c/ansi_c_language.h>
#include <langapi/language_util.h>
#include <langapi/mode.h>
#include <langapi/languages.h>

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>

#include <sstream>

#include <std_expr.h>
#include <prefix.h>

#include <util/find_symbols.h>

#include "summarization.h"

/*******************************************************************

 Function: summarizationt::create_program

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizationt::create_program(
  goto_programt &src,
  const exprt &invariant,
  goto_programt &dest) const
{
  exprt assume_expr;
  dest.instructions.clear();

  goto_programt::targett assume = dest.add_instruction(ASSUME);
  assume->guard=invariant;

  goto_programt::targett assert = dest.add_instruction(ASSERT);
  assert->guard=invariant;

  dest.instructions.splice(assert, src.instructions);

  // convenience..
  dest.update();

#if 0
  std::cout << std::endl << "SYMEX-PROGRAM:" << std::endl;
  for(goto_programt::instructionst::const_iterator it=
      dest.instructions.begin();
      it!=dest.instructions.end();
      it++)
  dest.output_instruction(ns, "", std::cout, it);
#endif
}


void summarizationt::prepare_program_with_transition_invariant(
  goto_programt &src,
  const var_mappingt &post_pre_map,
  const exprt &invariant,
  goto_programt &dest) const
{
  dest.instructions.clear( );

  // stub for assumptions on transition invariant
  goto_programt::targett assume = dest.add_instruction( ASSUME );

  // save pre-state
  for( var_mappingt::const_iterator it = post_pre_map.begin( ); it != post_pre_map.end( ); ++it )
  {
    goto_programt::targett assign = dest.add_instruction( ASSIGN );
    assign->code = code_assignt( it->second, it->first );
  }

  // another stub for assumptions on transition invariant
  goto_programt::targett assume2 = dest.add_instruction( ASSUME );

  // insert invariant as assertion
  goto_programt::targett assert = dest.add_instruction( ASSERT );
  assert->guard = invariant;

  // insert the loop body between the blocks
  dest.instructions.splice( assume2, src.instructions );

  // convenience..
  dest.update( );

#if 0
  std::cout << std::endl << "SYMEX-PROGRAM:" << std::endl;
  for(goto_programt::instructionst::const_iterator it=
      dest.instructions.begin();
      it!=dest.instructions.end();
      it++)
  dest.output_instruction(ns, "", std::cout, it);
#endif
}

/*******************************************************************\

 Function: string_summarizationt::test_invariant

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizationt::test_invariant(
  goto_programt &source,
  const exprt &invariant,
  const irep_idt &statname,
  loop_summaryt &summary)
{
  #if 0
  std::cout << "Testing invariant: " << expr2c(invariant, ns) << std::endl;
  #endif

  // save the instruction range
  goto_programt::targett first=source.instructions.begin();
  goto_programt::targett last=--source.instructions.end();

  fine_timet before=current_time();

  // this `steals' all instructions from source!
  goto_programt symex_prg;
  create_program(source, invariant, symex_prg);

  std::ofstream out;

  if(options.get_bool_option("save-loops"))
  {
    unsigned c = invariant_stats[statname].passed +
                 invariant_stats[statname].failed;

    std::string dname = stats_dir + "/loop_";
    dname += i2string(seen_loops) + "/";
    std::string fname = dname + statname.as_string() + "_" + i2string(c);

    out.open(fname.c_str(), std::fstream::out);
  }
  
  if (last_assertion_holds(ns.get_context(),
                           value_sets,
                           original_loop_head,
                           symex_prg, out,
                           max_mem_used,
                           options.get_bool_option("use-smt")))
  {
    assert(symex_prg.instructions.size()>0);

    summary.invariants.insert(invariant);
    invariant_stats[statname].passed++;
  }
  else
    invariant_stats[statname].failed++;

  if (options.get_bool_option("save-loops"))
    out.close();

  // `steal' the original instructions back!
  last++; // splice doesn't include the last one.
  source.instructions.splice(source.instructions.end(),
                             symex_prg.instructions,
                             first, last);

  invariant_stats[statname].time += (current_time()-before);
}


/*******************************************************************\

 Function: string_summarizationt::test_transition_invariant

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

termination_typet summarizationt::test_transition_invariant(
  goto_programt &source,
  const transition_invariantt &candidate,
  const irep_idt &statname,
  loop_summaryt &summary)
{
  const exprt & invariant = candidate.invariant;
  const var_mappingt & post_pre_map = candidate.mapping;

  #if 0
  std::cout << "Testing transition invariant: " << expr2c(invariant, ns) << std::endl;
  #endif

  termination_typet res = DOES_NOT_TERMINATE;
  // save the instruction range
  goto_programt::targett first=source.instructions.begin();
  goto_programt::targett last=--source.instructions.end();

  fine_timet before=current_time();

  // this `steals' all instructions from source!
  goto_programt symex_prg;
  prepare_program_with_transition_invariant(source, post_pre_map, invariant, symex_prg);

  std::ofstream out;

  if(options.get_bool_option("save-loops"))
  {
    unsigned c = invariant_stats[statname].passed +
                 invariant_stats[statname].failed;

    std::string dname = stats_dir + "/loop_";
    dname += i2string(seen_loops) + "/";
    std::string fname = dname + statname.as_string() + "_" + i2string(c);

    out.open(fname.c_str(), std::fstream::out);
  }

  if (last_assertion_holds(ns.get_context(),
                           value_sets,
                           original_loop_head,
                           symex_prg, out,
                           max_mem_used,
                           options.get_bool_option("use-smt")))
  {
    // if (is_compositional(invariant))
    summary.transition_invariants.push_back(candidate);
    invariant_stats[statname].passed++;
    res = TERMINATES;
  }
  else if (!candidate.assumptions.empty())
  {
    std::set<exprt> passed_assumptions;
    for( std::set<exprt>::const_iterator it = candidate.assumptions.begin( ); it != candidate.assumptions.end( ); ++it )
    {
      symex_prg.instructions.front().guard = *it;
      (++symex_prg.instructions.rbegin())->guard = *it;
      symex_prg.update();
      if (last_assertion_holds(ns.get_context(),
                                 value_sets,
                                 original_loop_head,
                                 symex_prg, out,
                                 max_mem_used,
                                 options.get_bool_option("use-smt")))
      {
        passed_assumptions.insert(*it);
      }
    }
    if( !passed_assumptions.empty( ) )
    {
      summary.transition_invariants.push_back( transition_invariantt( invariant, post_pre_map, passed_assumptions ) );
      invariant_stats[statname].passed++;
      res = TERMINATES_WITH_ASSUMPTION;
    }
    else
    {
      invariant_stats[statname].failed++;
    }
  }
  else
    invariant_stats[statname].failed++;

  if (options.get_bool_option("save-loops"))
    out.close();

  // `steal' the original instructions back!
  last++; // splice doesn't include the last one.
  source.instructions.splice(source.instructions.end(),
                             symex_prg.instructions,
                             first, last);

  invariant_stats[statname].time += (current_time()-before);
  return res;
}

/*******************************************************************\

 Function: summarizationt::print_statistics

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizationt::print_statistics(
    std::ostream &out) const
{
  out << "Results:" << std::endl;

  out << " Loops processed:\t\t" << seen_loops << "\tPASS\tFAIL\tTIME" <<
  std::endl;;

  for (invariant_statst::const_iterator it=invariant_stats.begin();
       it!=invariant_stats.end();
       it++)
  {
    const invariant_statt &stats=it->second;

    std::cout << " " << stats.long_name << " (" <<
      it->first << ")" << "\t\t" <<
      stats.passed + it->second.failed << "\t" <<
      stats.passed << "\t" <<
      stats.failed << "\t" <<
      time2string(stats.time) << std::endl;;
  }
}

/*******************************************************************\

 Function: summarizationt::get_variant

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizationt::get_variant(
  const goto_programt &program,
  loop_summaryt &summary) const
{
  std::set<exprt> &variant = summary.variant;
  std::set<exprt> &rhs_expressions = summary.rhs_expressions;

  forall_goto_program_instructions(it, program)
  {
    goto_programt::instructiont::labelst::const_iterator lit =
      find(it->labels.begin(), it->labels.end(), irep_idt("PRECONDITION_CHECK"));

    if (lit!=it->labels.end())
      continue;

    switch (it->type)
    {
      case NO_INSTRUCTION_TYPE:
      case FUNCTION_CALL:
      case RETURN:
      {
        assert(false); // this is supposed to be inlined!
        break;
      }
      case ASSIGN:
      {
        const code_assignt& code =
          to_code_assign(to_code(it->code));

        if((!(code.lhs().type().get("#constant")=="1") || 
             (code.lhs().type().has_subtype() && code.lhs().type().subtype().get("#constant")=="1")))
          variant.insert(code.lhs());

        rhs_expressions.insert(code.rhs());
        break;
      }
      case OTHER:
      {
        const codet code = to_code(it->code);

        if (code.get_statement()=="init")
          throw "unexpected assign in `other' code.";
        else if (code.get_statement()=="decl" ||
                 code.get_statement()=="free")
        {
          variant.insert(it->code.op0());
        }
        else if (it->code.get("statement")=="loop-summary")
          assert(false); // no loop summaries expected here.

        break;
      }
      case GOTO:
      case ASSUME:
      case ASSERT:
      {
        rhs_expressions.insert(it->guard);
        break;
      }
      case LOCATION:
      case DEAD:
      case SKIP:
      case END_FUNCTION:
      case ATOMIC_BEGIN:
      case ATOMIC_END:
      case START_THREAD:
      case END_THREAD:
      default: break; /* Nothing */
    }
  }
}

/*******************************************************************\

 Function: summarizationt::run_tests

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizationt::run_tests(
  goto_programt &source,
  loop_summaryt &summary)
{
//  termination_typet termination_status(DOES_NOT_TERMINATE);
//  bool is_terminating_with_precondition = false;

  fine_timet before=current_time();

  for( invariant_testst::iterator it = invariant_tests.begin( );
       it != invariant_tests.end( );
       it++ )
  {
    if( ( *it )->test_type == STATE )
    {
      std::set<exprt> potential_invariants;
      ( *it )->get_invariants( summary, potential_invariants );
      for( std::set<exprt>::const_iterator i_it = potential_invariants.begin( );
           i_it != potential_invariants.end( ); i_it++ )
        test_invariant( source, *i_it, ( *it )->short_name, summary );
    }
    else if( ( *it )->test_type == TRANSITION  || ( *it )->test_type == STATE_AND_TRANSITION)
    {
      transition_invariantst candidates;
      ( *it )->get_transition_invariants( summary, candidates );

      for( transition_invariantst::const_iterator i_it = candidates.begin( );
           i_it != candidates.end( ); i_it++ )
      {
        if(summary.termination_type == TERMINATES && options.get_bool_option( "termination" ))
          break; // enough, we've proven termination

        termination_typet termination_status = test_transition_invariant( source, *i_it, ( *it )->short_name, summary );
        if (termination_status > summary.termination_type)
          summary.termination_type = termination_status;
      }
    }
  }

//  if( termination_status )
//    summary.termination_type = TERMINATES;
//  else if( is_terminating_with_precondition && summary.termination_type != TERMINATES )
//    summary.termination_type = TERMINATES_WITH_ASSUMPTION;

  if( options.get_bool_option( "termination" ) )
  {
    switch( summary.termination_type )
    {
    case TERMINATES:
      std::cout << " - Loop terminates";
      break;
    case TERMINATES_WITH_ASSUMPTION:
      std::cout << " - Loop terminates with assumption";
      break;
    case DOES_NOT_TERMINATE:
    default:
      std::cout << " - Loop (possibly) does not terminate";
    }
    std::cout << " (analysis time: " << (double)(current_time()-before)/1000 << " sec.)" << std::endl;
  }
  
  if (options.get_bool_option("interactive"))
  {
    std::set<exprt> user_invariants;
    std::cout <<"\rPlace your invariant candidates in user.inv, press any key and Enter afterwards: ";
    char t;
    std::cin >> t;

    get_user_invariants_fromfile(user_invariants);
    invariant_stats["UD"].long_name = "User Defined";

    for (std::set<exprt>::const_iterator i_it = user_invariants.begin();
        i_it != user_invariants.end(); i_it++)
    {
      test_invariant(source, *i_it, "UD", summary);
    }
  }
}

/*******************************************************************\

 Function: summarizationt::run_tests

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

summarizationt::~summarizationt( void )
{
  // all test objects get destroyed when we're done.
  for(invariant_testst::iterator it=invariant_tests.begin();
      it!=invariant_tests.end();
      )
  {
    delete *it;
    it = invariant_tests.erase(it);
  }
}

/*******************************************************************\

 Function: summarizationt::summarize_loop

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizationt::summarize_loop(
  goto_programt::const_targett &original_head,
  goto_programt &source,
  loop_summaryt &summary)
{
  new_loop_number();
  original_loop_head = original_head;

  summary.loop_head = source.instructions.begin();
  get_variant(source, summary);

  if (!options.get_bool_option("no-invariants"))
  {
    if(options.get_bool_option("incremental"))
      run_tests_incremental(source, summary);
    else
      run_tests(source, summary);
  }
}

/*******************************************************************\

 Function: summarizationt::schedule

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizationt::schedule(
  invariant_testt* test)
{
  invariant_stats[test->short_name].long_name = test->long_name;
  invariant_tests.push_back(test);
}

/*******************************************************************\

 Function: summarizationt::run_tests_incremental

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizationt::run_tests_incremental(
  goto_programt &source,
  loop_summaryt &summary)
{
  contextt temp_context;
  namespacet ns(context, temp_context);
  symex_target_equationt equation(ns);
  std::ofstream out;

  if(options.get_bool_option("save-loops"))
  {
    std::string dname = stats_dir + "/loop_" +
                        i2string(seen_loops) + "/symex_equation";
    out.open(dname.c_str(), std::fstream::out);
  }

  symex_assertiont symex(value_sets, original_loop_head,
                         ns, context, equation);

  get_loop_equation(temp_context, symex, source, equation, out);

  if (options.get_bool_option("save-loops"))
  {
    equation.output(out);
    out.close();
  }

  // run the actual tests

  for(invariant_testst::iterator it=invariant_tests.begin();
      it!=invariant_tests.end();
      it++)
  {
    std::set<exprt> potential_invariants;
    (*it)->get_invariants(summary, potential_invariants);

    for(std::set<exprt>::const_iterator i_it=potential_invariants.begin();
        i_it!=potential_invariants.end();
        i_it++)
    {
      #if 0
      std::cout << "Testing invariant: " << expr2c(invariant, ns) << std::endl;
      #endif

      const irep_idt &statname = (*it)->short_name;
      const exprt &invariant = *i_it;

      if(options.get_bool_option("save-loops"))
      {
        unsigned c = invariant_stats[statname].passed +
                     invariant_stats[statname].failed;

        std::string dname = stats_dir + "/loop_";
        dname += i2string(seen_loops) + "/";
        std::string fname = dname + statname.as_string() + "_" + i2string(c);

        out.open(fname.c_str(), std::fstream::out);
      }

      fine_timet before=current_time();

      symex_target_equationt eq_copy = equation;
      guardt guard;

      guard.add(eq_copy.SSA_steps.back().guard_expr);

      exprt temp(invariant);
      eq_copy.assertion(guard, temp, "invariant candidate",
                        symex_targett::sourcet());

      // push an assumption into the front of the equation
      eq_copy.SSA_steps.push_front(symex_target_equationt::SSA_stept());
      symex_target_equationt::SSA_stept &state=eq_copy.SSA_steps.front();

      state.guard_expr.make_true();
      state.lhs.make_nil();
      state.cond_expr = invariant;
      state.type=goto_trace_stept::ASSUME;

      if(symex.equation_holds(eq_copy, out, max_mem_used,
                              options.get_bool_option("use-smt")))
      {
        summary.invariants.insert(invariant);
        invariant_stats[statname].passed++;
      }
      else
        invariant_stats[statname].failed++;

      if (options.get_bool_option("save-loops"))
        out.close();

      invariant_stats[statname].time += (current_time()-before);
    }
  }

  if (options.get_bool_option("save-loops"))
    out.close();
}

/*******************************************************************\

 Function: summarizationt::run_tests

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizationt::get_loop_equation(
  contextt &temp_context,
  symex_assertiont &symex,
  goto_programt &source,
  symex_target_equationt &equation,
  std::ofstream &out)
{
  goto_programt::const_targett last=--source.instructions.end();

  symex.to_equation(context, temp_context, value_sets, original_loop_head,
                    source, last, equation, out, max_mem_used,
                    options.get_bool_option("use-smt"));
}


/*******************************************************************\

 Function: summarizationt::get_user_invariants_fromfile

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void summarizationt::get_user_invariants_fromfile(std::set<exprt> &user_invariants)
{
  std::ifstream infile("user.inv");

  if(!infile)
    throw std::string("failed to open user.inv");

  // use mode from main sequent

  languaget *l;

  {
    #if 0
    int mode;
    if(sequent.mode!="" &&
       (mode=get_mode(sequent.mode))!=-1)
      l=new_language(mode);
    else
    #endif
      l=new ansi_c_languaget;
  }

  // use auto_ptr because of the exceptions
  std::auto_ptr<languaget> language(l);

  std::string line;

  while(str_getline(infile, line))
  {
    if(line!="" && line[0]!='#' &&
       std::string(line, 0, 2)!="//")
    {
      exprt expr;
      stream_message_handlert mh(std::cout);
      if(language->to_expr(line, "", expr, mh, ns))
        throw "failed to parse `"+line+"'";

      if(expr.type().id()!="bool")
      {
        std::string type_string;
        language->from_type(expr.type(), type_string, ns);
        throw "expected boolean expression as predicate, but got "+type_string;
      }

      user_invariants.insert(expr);
    }
  }
}


bool summarizationt::is_compositional( const exprt &disjunction)
{

//  std::stringstream msg;
//  std::cout << "Checking compositionality of: " << from_expr(ns, "", disjunction) << std::endl;
//  debug(msg.str());

  std::set<exprt> symbols;
  find_symbols(disjunction, symbols);

  // Get a proper pre/post-mapping
  replace_idt varmap;
  get_pre_post(symbols, varmap);


  satcheckt checker;
  stream_message_handlert message_handler(std::cout);
  checker.set_message_handler(message_handler);
  bv_pointerst converter(ns, checker);

  std::set<exprt> new_symbols;

  exprt d_post1 = disjunction; replace_idt p1_replacer;
  exprt d_post2 = disjunction; replace_idt p2_replacer;

  for(replace_idt::const_iterator it=varmap.begin();
      it!=varmap.end();
      it++)
  {
    const irep_idt &pre = it->first;
    const irep_idt &post = it->second;

    p1_replacer.insert(post, "LINK::"+post.as_string());
    p2_replacer.insert(pre,  "LINK::"+post.as_string());
  }

  p1_replacer.replace(d_post1);
  p2_replacer.replace(d_post2);

  #if 0
  std::cout << "1st: " << d_post1 << std::endl;
  std::cout << "2nd: " << d_post2 << std::endl;
  #endif

  exprt post = and_exprt(d_post1, d_post2);
  implies_exprt f( post, disjunction );

  #if 0
  std::cout << "Check: " << from_expr(ns, "", f) << std::endl;
  #endif

  converter.set_to_true(not_exprt( f ));

  bv_pointerst::resultt res = converter.dec_solve();

  if (res != decision_proceduret::D_SATISFIABLE &&
      res != decision_proceduret::D_UNSATISFIABLE)
    throw "SAT SOLVER PROBLEM";

  return res==decision_proceduret::D_UNSATISFIABLE;
}

/********************************************************************\

 Function: summarizationt::get_pre_post

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void summarizationt::get_pre_post(
    const std::set<exprt> &symbols,
    replace_idt &varmap) const
{
  varmap.clear();

  for(std::set<exprt>::const_iterator it=symbols.begin();
      it!=symbols.end();
      it++)
  {
    irep_idt id = it->get(ID_identifier);
    const std::string &id_s = id.as_string();
    if (has_prefix(id_s, "termination"))
      varmap.insert(id, ID_nil);
  }

  for(std::set<exprt>::const_iterator it=symbols.begin();
      it!=symbols.end();
      it++)
  {
    irep_idt id = it->get(ID_identifier);
    const std::string &id_s = id.as_string();
    if (!has_prefix(id_s, "termination"))
    {
      // This is an instrumented variable; we should have a
      // corresponding pre-variable in varmap now.
      for (replace_idt::iterator vit=varmap.begin();
           vit!=varmap.end();
           vit++)
      {
        const irep_idt &pre = vit->first;
        if (pre.as_string().find(id_s)!=std::string::npos)
        {
          vit->second = id;
          break;
        }
      }
    }
  }

  #ifdef _DEBUG
  for (replace_idt::iterator vit=varmap.begin();
       vit!=varmap.end();
       vit++)
  {
    assert(vit->second != ID_nil);
  }
  #endif
}
