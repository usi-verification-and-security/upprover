/*******************************************************************\
 
Module: loop classification for Loopfrog: string class
 
Author: Daniel Kroening
        CM Wintersteiger
 
Date: June 2007
 
\*******************************************************************/

#include <fstream>
#include <std_code.h>

#include "class_string.h"
#include "string_utils.h"

/*******************************************************************\
 
Function: class_stringt::class_stringt
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/
class_stringt::class_stringt(const value_propagation_fivrt &vp) : 
  class_baset(vp)   
{ 
  for (int i=0; i<8; i++) 
    { binsR[i]=binsW[i]=binsRW[i]=0; } 
  recognizedR=recognizedW=recognizedRW=0; 
  constR=constW=constRW=0;
  R1W1loops=0;
  
  std::ofstream f("loops-0-1", std::ios::out); f.close();
}

/*******************************************************************\
 
Function: class_stringt::recognize
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/
bool class_stringt::recognize( 
  const contextt& context, 
  const goto_programt& program,
  goto_programt::const_targett &begin,
  goto_programt::const_targett &end)
{
  find_symbols_sett read_strings;
  find_symbols_sett written_strings;
  
  goto_programt::const_targett i=begin;
  do
  {
    //const value_sett &vset = value_prop.lookup(i);
    const value_sett vset;
     
    switch (i->type)
    {
      case NO_INSTRUCTION_TYPE: {
        throw "Unknown instruction type encountered.";
        break; 
      }
      case GOTO: 
      case ASSUME: 
      case ASSERT: {
        find_string_type_symbols(i->guard, vset, read_strings);
        break; 
      }
      case OTHER:
      case RETURN: {         
        find_string_type_symbols(i->code, vset, read_strings);
        break; 
      }
      case ASSIGN: { 
        const code_assignt& code = to_code_assign(to_code(i->code)); 
        const exprt& lhs = code.lhs();
        const exprt& rhs = code.rhs();
        
        if (lhs.id()=="dereference" || lhs.id()=="index")
          find_string_type_symbols(lhs, vset, written_strings);
        find_string_type_symbols(rhs, vset, read_strings);
        break;
      }
      case FUNCTION_CALL: { 
        const code_function_callt& code = 
          to_code_function_call(to_code(i->code));
        const exprt& lhs = code.lhs();        
        const exprt::operandst& arguments = code.arguments();
        
        if (lhs.id()=="dereference" || lhs.id()=="index")
          find_string_type_symbols(lhs, vset, written_strings);
        
        for(exprt::operandst::const_iterator it=arguments.begin();
            it!=arguments.end();
            it++)
        {
          find_string_type_symbols(*it, vset, read_strings);
        }
        break; 
      }
            
      case LOCATION:
      case SYNC:
      case SKIP:
      case END_FUNCTION:
      case ATOMIC_BEGIN: 
      case ATOMIC_END:
      case START_THREAD: 
      case END_THREAD:
      default: break; /* Nothing */
    }
  } while(i++!=end);
  
//  write_loop_symbols_file(read_strings, written_strings, begin, end);

  if (written_strings.size()==0 && read_strings.size()==1)
  {
    save_loop("loops-0-1", context, program, begin, end);
    R1W1loops++;
  }
  
  if (written_strings.size()!=0) // writing loop
  {
    if (read_strings.size()!=0) // it also reads
    {
      unsigned totalsize = written_strings.size() + read_strings.size();  
      if (totalsize>6)
        binsRW[7]++;
      else
        binsRW[totalsize]++;        
      recognizedRW++;
      
      if ( 
        (find(written_strings.begin(), written_strings.end(), "CONSTANTS")
        !=written_strings.end()) &&
        (find(read_strings.begin(), read_strings.end(), "CONSTANTS")
        !=read_strings.end())
        )
      constRW++;      
    }
    else // write-only loop
    {
      if (written_strings.size()>6)
        binsW[7]++;
      else
        binsW[written_strings.size()]++;
      recognizedW++;
      
      if (find(written_strings.begin(), written_strings.end(), "CONSTANTS")
          !=written_strings.end())
        constW++;
    }        
      
    return true;
  }
  else if (read_strings.size()!=0) // read-only loop
  {
    if (read_strings.size()>6)
      binsR[7]++;
    else
      binsR[read_strings.size()]++;    
    recognizedR++;
    
    if (find(read_strings.begin(), read_strings.end(), "CONSTANTS")
        !=read_strings.end())
      constR++;
      
    return true;
  }
  
  return false; // not a string loop
}

/*******************************************************************\
 
Function: class_stringt::report
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/
void class_stringt::report( std::ostream& out )
{
  out << "String Loops tot.  : " << recognized << std::endl;
  out << "String Loops (W)   : " << recognizedW << std::endl;  
  out << "# of variables (W) : ";
  for (int i=0;i<7;i++) out << i << "V=" << binsW[i] << " ";
  out << "7+V=" << binsW[7] << std::endl;
  out << "String Loops (R)   : " << recognizedR << std::endl;  
  out << "# of variables (R) : ";
  for (int i=0;i<7;i++) out << i << "V=" << binsR[i] << " ";
  out << "7+V=" << binsR[7] << std::endl;
  out << "String Loops (RW)  : " << recognizedRW << std::endl;  
  out << "# of variables (RW): ";
  for (int i=0;i<7;i++) std::cout << i << "V=" << binsRW[i] << " ";
  out << "7+V=" << binsRW[7] << std::endl;
  out << "Str. constant loops: R=" << constR << " W=" << constW << " RW=" <<
    constRW << std::endl;
  out << "R1W1loops: " << R1W1loops << std::endl;
}

/*******************************************************************\
 
Function: class_stringt::write_loop_symbols_file
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/
void class_stringt::write_loop_symbols_file( 
  const find_symbols_sett &read_strings,
  const find_symbols_sett &written_strings,
  goto_programt::const_targett &begin,
  goto_programt::const_targett &end)
{
  if (written_strings.size()>0 || read_strings.size()>0)
  {
    std::ofstream f("string_symbols", std::ios::app);
    f << "Loop from " << 
      (begin->location.is_nil()?"UNKNOWN":begin->location.as_string()) << 
      std::endl;
    f << "Loop to   " << 
      (end->location.is_nil()?"UNKNOWN":end->location.as_string()) << 
      std::endl;
    f << "---written" << std::endl;
    for (find_symbols_sett::const_iterator it=written_strings.begin();
         it!=written_strings.end();
         it++)
    {
      f << *it << std::endl;
    }
    f << "------read" << std::endl;
    for (find_symbols_sett::const_iterator it=read_strings.begin();
         it!=read_strings.end();
         it++)
    {
      f << *it << std::endl;
    }
    f << "----------" << std::endl << std::endl;  
    f.close();
  }
}
