#include <time_stopping.h>
#include <goto-programs/read_goto_binary.h>

#include "arith_tools.h"
#include "fixedbv.h"
#include "ieee_float.h"

goto_functionst goto_functions_1;
goto_functionst goto_functions_2;

//std::vector<goto_programt::const_targett* > goto_unrolled_1;
//std::vector<goto_programt::const_targett* > goto_unrolled_2;
//std::vector<goto_programt::const_targett* > goto_common;

/*std::vector<std::string >*/ std::string goto_unrolled_1;
/*std::vector<std::string >*/ std::string goto_unrolled_2;
//std::vector<std::string > goto_common;

std::vector<std::pair<const irep_idt*, bool> > functions;

std::string form(const exprt &expr)
{
  if (expr.has_operands()){
    if (expr.type().id()==ID_signedbv){
      std::string res = expr.id_string();
      for (unsigned i = 0; i < expr.operands().size(); i++){
        res = res + " " + form(expr.operands()[i]);
      }
      return res;
    }
  }

  if(expr.is_constant())
  {
    if(expr.type().id()==ID_natural ||
       expr.type().id()==ID_integer ||
       expr.type().id()==ID_unsignedbv ||
       expr.type().id()==ID_signedbv)
    {
      mp_integer i;
      if(to_integer(expr, i)) return "(number conversion failed)";

      return integer2string(i);
    }
//    else if(expr.type().id()==ID_fixedbv)
//    {
//      return fixedbvt(expr);
//    }
//    else if(expr.type().id()==ID_floatbv)
//    {
//      return ieee_floatt(expr);
//    }
  }
  else if(expr.id()==ID_string_constant){
    return expr.get_string(ID_value);
  } else if (expr.id()==ID_symbol){
    return expr.get("identifier").as_string();
  }
  return "(not supported yet: "+expr.id_string()+")";
}

std::string cmd_str (goto_programt::const_targett &it)
{
  std::string res;
  switch(it->type)
    {
      case SKIP: break;
      case END_FUNCTION: break;
      case LOCATION:  break;
      case GOTO: break;
      case ASSUME:  break;
      case ASSERT:  break;
      case RETURN:  break;
      case ASSIGN: {
          const code_assignt &ass =
              to_code_assign(it->code);
          res = (ass.lhs().get("identifier").as_string() + " = " + form(ass.rhs()));
        }
        break;
      case FUNCTION_CALL: {
          const code_function_callt &call =
              to_code_function_call(to_code(it->code));

          // TODO: add arguments here
          res = call.function().get("identifier").as_string();
      }
      case OTHER:  break;
      case DECL:  break;
      case DEAD:  break;
      case START_THREAD:
        throw "START_THREAD not yet implemented";
      case END_THREAD:  break;
      case ATOMIC_BEGIN:
      case ATOMIC_END:  break;
      default:
        assert(false);
      }
  return res;
}

void collect_functions(const goto_functionst &goto_functions, const goto_programt &program,
    std::vector<std::pair<const irep_idt*, bool> >  &functions)
{
  for(goto_programt::const_targett it = program.instructions.begin();
      it!=program.instructions.end(); ++it)
  {
    if(it->type == FUNCTION_CALL)
    {
       const code_function_callt &call =
         to_code_function_call(to_code(it->code));

       const irep_idt &name = call.function().get("identifier");

       std::pair<const irep_idt*, bool> p = std::make_pair(&name, true);

       functions.push_back(p);

       goto_functionst::function_mapt::const_iterator f_it =
           goto_functions.function_map.find(name);

       if(f_it!=goto_functions.function_map.end())
       {
         collect_functions(goto_functions, f_it->second.body, functions);
       }
    }
  }
}


bool is_untouched(const irep_idt &name)
{
  for (unsigned i = 0; i < functions.size(); i++){
    if ((*functions[i].first) == name){
      if (functions[i].second == false){
        return false;
      }
    }
  }
  return true;
}

bool unroll_goto(goto_functionst &goto_functions, const irep_idt &name,
                 std::string &goto_unrolled)
{
  goto_unrolled = "";
  if (!is_untouched (name)){
    return false;
  }
  const goto_programt& program = goto_functions.function_map[name].body;
  for(goto_programt::const_targett it = program.instructions.begin();
      it!=program.instructions.end(); ++it)
  {
    if(it->type == FUNCTION_CALL){
      const code_function_callt &call =
        to_code_function_call(to_code(it->code));

      const irep_idt &name_child = call.function().get("identifier");

      if (!is_untouched(name_child)){
        return false;   // the nested function was modified => this function is also modified
      }
    }
    goto_unrolled = goto_unrolled + "; " + cmd_str(it);
  }
  return true;
}

int main(int argc, const char** argv) {

  fine_timet before, after;
  stream_message_handlert mh(std::cout);

  // Stage 1: Load file 1

  contextt context_1;
  std::cout << "#1: Loading " << argv[1] << " ...\n";
  before=current_time();
  if(read_goto_binary(argv[1], context_1, goto_functions_1, mh))
  {
    std::cerr << "Error reading file " << argv[1] << ".\n";
    return 1;
  }
  after=current_time();
  std::cout << "    LOAD Time: " << time2string(after-before) << " sec.\n";
  
  // Stage 2: Load file 2

  contextt context_2;
  std::cout << "#2: Loading " << argv[2] << "' ...\n";
  before=current_time();
  if(read_goto_binary(argv[2], context_2, goto_functions_2, mh))
  {
    std::cerr << "Error reading file " << argv[2] << ".\n";
    return 1;
  }
  after=current_time();
  std::cout << "    LOAD Time: " << time2string(after-before) << " sec.\n";

  // Stage 3: Analyze both files

  before=current_time();
  collect_functions(goto_functions_1, goto_functions_1.function_map["main"].body, functions);

  for (unsigned i = functions.size() - 1; i > 0; i--)
  {
    bool pre_res_1 = unroll_goto(goto_functions_1, (*functions[i].first), goto_unrolled_1);
    bool pre_res_2 = unroll_goto(goto_functions_2, (*functions[i].first), goto_unrolled_2);

    bool pre_res_3 = false;
    if (pre_res_1 && pre_res_2){
      //std::cout << goto_unrolled_1 << "\n" << goto_unrolled_2 <<"\n";
      if (goto_unrolled_1 == goto_unrolled_2){
        pre_res_3 = true;
      }
    }

    if (pre_res_3 == false){
      functions[i].second = false;
    }

    std::cout << "is \"" << (*functions[i].first) << "\" untouched? (0 = no / 1 = yes): " << functions[i].second << "\n";
  }
  after=current_time();
  std::cout << "    PROCESSING Time: " << time2string(after-before) << " sec.\n";
}
