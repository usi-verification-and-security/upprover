/*******************************************************************\
 
Module: loop classification for Loopfrog
 
Author: Daniel Kroening
        CM Wintersteiger
 
Date: June 2007
 
\*******************************************************************/

#include "loop_classifier.h"

/*******************************************************************\
 
Function: loop_classifiert::classify
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/

void loop_classifiert::classify( 
  const contextt &context, 
  const goto_functionst &functions)
{
  total_loops=0;
  total_statements=0;  
  strcmp_calls = strcpy_calls = strcat_calls = strncmp_calls =    
  strncpy_calls = strncat_calls = strtok_calls = 0;  
  
  for (goto_functionst::function_mapt::const_iterator fit =
         functions.function_map.begin();
       fit!=functions.function_map.end();
       fit++)
  {
//    if (fit->second.body_available)
//      std::cout << fit->first << ": " << std::endl;       
    classify(context, fit->second);
  }  
    
  for (unsigned i=0; i<79; i++) std::cout << "="; std::cout << std::endl;
  instr_string.report(std::cout);
  for (unsigned i=0; i<79; i++) std::cout << "-"; std::cout << std::endl;
  instr_charsearch.report(std::cout);
  instr_nocharsearch.report(std::cout);
  for (unsigned i=0; i<79; i++) std::cout << "-"; std::cout << std::endl;  
  report_calls(std::cout);
  for (unsigned i=0; i<79; i++) std::cout << "-"; std::cout << std::endl;
  std::cout << "Non-String loops: " << total_loops - instr_string.recognized << 
    "\tTotal loops   : " << total_loops << "\tString Loop Ratio: " << 
    std::setprecision(3) <<
    100*instr_string.recognized/(double) total_loops << "%" << std::endl;  
  std::cout << "Statements      : " << total_statements << std::endl;
  for (unsigned i=0; i<79; i++) std::cout << "="; std::cout << std::endl;
}

/*******************************************************************\
 
Function: loop_classifiert::instrument
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/

void loop_classifiert::instrument( 
  contextt &context, 
  goto_functionst &functions)
{
  for (goto_functionst::function_mapt::iterator fit =
         functions.function_map.begin();
       fit!=functions.function_map.end();
       fit++)
  {
    instrument(context, fit->second);
  }  
}

/*******************************************************************\
 
Function: loop_classifiert::classify
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/

void loop_classifiert::classify( 
  const contextt &context, 
  const goto_functiont &function)
{  
  forall_goto_program_instructions(it, function.body)
  {
    if (it->is_backwards_goto())
    {
      if (it->targets.size()==0)
        throw ("Nil-Target Goto encountered.");
      else if (it->targets.size()>1)
        throw ("Multi-Target Goto encountered.");
      else
      {
        goto_programt::const_targett t=it->targets.front();
        classify( context, function.body, t, it );       
      }
    }
    
    total_statements++;
    check_call(context, it);
    
  }    
}

/*******************************************************************\
 
Function: loop_classifiert::instrument
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/

void loop_classifiert::instrument( 
  contextt &context, 
  goto_functiont &function)
{  
  Forall_goto_program_instructions(it, function.body)
  {
    if (it->is_backwards_goto())
    {
      if (it->targets.size()==0)
        throw ("Nil-Target Goto encountered.");
      else if (it->targets.size()>1)
        throw ("Multi-Target Goto encountered.");
      else
      {
        goto_programt::targett t=it->targets.front();
        instrument( context, function.body, t, it );
      }
    }
  }    
}

/*******************************************************************\
 
Function: loop_classifiert::classify
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/

void loop_classifiert::classify( 
  const contextt& context, 
  const goto_programt& program,
  goto_programt::const_targett &begin,
  goto_programt::const_targett &end )
{
  total_loops++;
  instr_string.classify(context, program, begin, end);   
  instr_charsearch.classify(context, program, begin, end);
  instr_nocharsearch.classify(context, program, begin, end);
}

/*******************************************************************\
 
Function: loop_classifiert::instrument
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/

void loop_classifiert::instrument( 
  contextt& context, 
  goto_programt& program,
  goto_programt::targett &begin,
  goto_programt::targett &end )
{
  instr_string.add_instrumentation(context, program, begin, end);   
  instr_charsearch.add_instrumentation(context, program, begin, end);
  instr_nocharsearch.add_instrumentation(context, program, begin, end);
}

/*******************************************************************\
 
Function: loop_classifiert::check_call
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/

void loop_classifiert::check_call(
  const contextt& context,
  goto_programt::const_targett& it)
{
  if (it->is_function_call())
  {
    const code_function_callt& code = 
      to_code_function_call(to_code(it->code));
    const irep_idt &id = code.function().get("identifier");
    if (id=="c::strcmp")
    {
      symbolst::const_iterator si = context.symbols.find(id);
      if (si==context.symbols.end() || si->second.value.is_nil())
        strcmp_calls++;        
    } else if (id=="c::strcpy")
    {
      symbolst::const_iterator si = context.symbols.find(id);
      if (si==context.symbols.end() || si->second.value.is_nil())
        strcpy_calls++;  
    } else if (id=="c::strcat")
    {
      symbolst::const_iterator si = context.symbols.find(id);
      if (si==context.symbols.end() || si->second.value.is_nil())
        strcat_calls++;  
    } else if (id=="c::strncmp")
    {
      symbolst::const_iterator si = context.symbols.find(id);
      if (si==context.symbols.end() || si->second.value.is_nil())
        strncmp_calls++;  
    } else if (id=="c::strncpy")
    {
      symbolst::const_iterator si = context.symbols.find(id);
      if (si==context.symbols.end() || si->second.value.is_nil())
        strncpy_calls++;  
    } else if (id=="c::strncat")
    {
      symbolst::const_iterator si = context.symbols.find(id);
      if (si==context.symbols.end() || si->second.value.is_nil())
        strncat_calls++;  
    } else if (id=="c::strtok")
    {
      symbolst::const_iterator si = context.symbols.find(id);
      if (si==context.symbols.end() || si->second.value.is_nil())
        strtok_calls++;  
    }
  }
}

/*******************************************************************\
 
Function: loop_classifiert::report_calls
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/

void loop_classifiert::report_calls(std::ostream& out)
{
  out << "strcmp calls : " << strcmp_calls << "\t";
  out << "strcpy calls : " << strcpy_calls << "\t";
  out << "strcat calls : " << strcat_calls << std::endl;
  out << "strncmp calls: " << strncmp_calls << "\t";
  out << "strncpy calls: " << strncpy_calls << "\t";
  out << "strncat calls: " << strncat_calls << std::endl;
  out << "strtok calls : " << strtok_calls << std::endl;
}
