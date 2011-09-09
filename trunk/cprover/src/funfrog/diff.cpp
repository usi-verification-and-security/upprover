#include <time_stopping.h>
#include <goto-programs/read_goto_binary.h>

#include "arith_tools.h"
#include "fixedbv.h"
#include "ieee_float.h"

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
      case RETURN: {
          const code_returnt &ret =
            to_code_return(it->code);
          res = form(ret.return_value());
        }
        break;
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
      std::vector<std::string > &goto_unrolled, bool inherit_change)
{
  if (!is_untouched (name)){
    return false;
  }
  const goto_programt& program = goto_functions.function_map[name].body;
  for(goto_programt::const_targett it = program.instructions.begin();
      it!=program.instructions.end(); ++it)
  {
    if(it->type == FUNCTION_CALL && inherit_change){
      const code_function_callt &call =
        to_code_function_call(to_code(it->code));

      const irep_idt &name_child = call.function().get("identifier");

      if (!is_untouched(name_child)){
        return false;   // the nested function was modified => this function is also modified
      }
    }
    goto_unrolled.push_back(cmd_str(it));
  }
  return true;
}

void copy(std::vector<std::string > &goto_1,
    std::vector<std::string > &goto_2){
  for (unsigned i = 0; i < goto_2.size(); i++){
    goto_1.push_back(goto_2[i]);
  }
}

bool compare_str_vecs(std::vector<std::string > &goto_unrolled_1,
                      std::vector<std::string > &goto_unrolled_2){
  unsigned size_1 = goto_unrolled_1.size();
  unsigned size_2 = goto_unrolled_2.size();

  if (size_1 == 0 && size_2 == 0){
    return true;
  } else if (size_1 == 0 || size_2 == 0){
    return false;
  }

  std::vector<std::string > **goto_common_s =
      new std::vector<std::string >*[size_1 + 1];
  for (unsigned i = 0; i <= size_1; ++i){
    goto_common_s[i] = new std::vector<std::string >[size_2 + 1];
  }
  for (unsigned i = 1; i <= size_1; i++){
    for (unsigned j = 1; j <= size_2; j++){
      std::vector<std::string >& tmp_i_j = goto_common_s[i][j];
      if (goto_unrolled_1[i-1] == goto_unrolled_2[j-1]){
        tmp_i_j.push_back(goto_unrolled_1[i-1]);
        copy(tmp_i_j, goto_common_s[i-1][j-1]);
      } else {
        std::vector<std::string >& tmp_i_1_j = goto_common_s[i-1][j];
        std::vector<std::string >& tmp_i_j_1 = goto_common_s[i][j-1];

        if (tmp_i_j_1.size() > tmp_i_1_j.size()){
          copy(tmp_i_j, tmp_i_j_1);
        } else {
          copy(tmp_i_j, tmp_i_1_j);
        }
      }
    }
  }

  std::vector<std::string > goto_common = goto_common_s[size_1][size_2];
  unsigned size_c = goto_common.size();
  bool res = size_1 == size_2 && size_c == size_1 && size_c == size_2;

//  if (!res){
//    std::cout << "Finally: "
//              << size_1 << " " << size_2 << " " << size_c << "\n";
//    for (unsigned i = 0; i < size_c; i++){
//      std::cout <<"[" <<i<< "]" << goto_common[i] <<"\n";
//    }
//  }

  return res;
}

int main(int argc, const char** argv) {

  fine_timet before, after;
  stream_message_handlert mh(std::cout);

  goto_functionst goto_functions_1;
  goto_functionst goto_functions_2;

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
  collect_functions(goto_functions_2, goto_functions_2.function_map["main"].body, functions);

  std::vector<std::string > goto_unrolled_1;
  std::vector<std::string > goto_unrolled_2;

  for (unsigned i = functions.size() - 1; i > 0; i--)
  {
    std::cout << "is \"" << (*functions[i].first);

    bool pre_res_1 = unroll_goto(goto_functions_1, (*functions[i].first), goto_unrolled_1, false);
    bool pre_res_2 = unroll_goto(goto_functions_2, (*functions[i].first), goto_unrolled_2, false);

    bool pre_res_3 = false;
    if (pre_res_1 && pre_res_2){
      if (compare_str_vecs (goto_unrolled_1, goto_unrolled_2)){
        pre_res_3 = true;
      }
    }

    if (pre_res_3 == false){
      functions[i].second = false;
    }

    std::cout << "\" untouched? (0 = no / 1 = yes): " << functions[i].second << "\n";
    goto_unrolled_1.clear();
    goto_unrolled_2.clear();
  }
  after=current_time();
  std::cout << "    PROCESSING Time: " << time2string(after-before) << " sec.\n";
}
