#include <time_stopping.h>
#include <goto-programs/read_goto_binary.h>

#include "arith_tools.h"
#include "fixedbv.h"
#include "ieee_float.h"

std::vector<std::pair<const irep_idt*, bool> > functions;

std::string form(const exprt &expr)
{
  if (expr.has_operands()){
    std::string res = expr.id_string();
    for (unsigned i = 0; i < expr.operands().size(); i++){
      res = res + " " + form(expr.operands()[i]);
    }
    return res;
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
      case SKIP:  { res = "skip"; } break;
      case END_FUNCTION: { res = "end_f"; } break;
      case LOCATION:   { res = "loc + ?"; } break;      // TODO
      case GOTO:  { res = "goto _ ?"; } break;          // TODO
      case ASSUME:   { res = "assume ?"; } break;       // TODO
      case ASSERT:  { res = "assert ?"; }  break;       // TODO
      case RETURN: {
          const code_returnt &ret = to_code_return(it->code);
          res = "return " + form(ret.return_value());
        }
        break;
      case ASSIGN: {
          const code_assignt &ass =
              to_code_assign(it->code);
          res = (ass.lhs().get("identifier").as_string() + " = " + form(ass.rhs()));
        }
        break;
      case FUNCTION_CALL: {
          const code_function_callt &call = to_code_function_call(to_code(it->code));
          res = call.function().get("identifier").as_string();

          for (unsigned i = 0; i < call.arguments().size(); i++){
            res = res + " (" + form (call.arguments()[i]) + ")";
          }
      }
      case OTHER:   { res = "other ?"; } break;         // TODO
      case DECL: {
          const code_declt &decl = to_code_decl(it->code);
          res = form (decl);
        }
        break;
      case DEAD:  { res = "dead ?"; }  break;           // TODO
      case START_THREAD:
        throw "START_THREAD not yet implemented";
      case END_THREAD:  { res = "end_th"; }  break;     // TODO
      case ATOMIC_BEGIN: { res = "atomic_beg"; }        // TODO
      case ATOMIC_END: { res = "atomic_end"; }   break; // TODO
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

       functions.push_back(std::make_pair(&name, true));

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

void do_diff(std::vector<std::string > &goto_unrolled_1,
             std::vector<std::string > &goto_unrolled_2,
             std::vector<std::string > &goto_common)
{
  // sizes
  unsigned size_1 = goto_unrolled_1.size();
  unsigned size_2 = goto_unrolled_2.size();
  unsigned size_c = goto_common.size();

  // iterators
  unsigned i_1 = 0;
  unsigned i_2 = 0;
  unsigned i_c = size_c;
  while (i_2 < size_2){
    while(i_1 < size_1 && i_c > 0 && goto_unrolled_1[i_1] != goto_common[i_c - 1]){
      std::cout << "    [-] " << goto_unrolled_1[i_1] << "\n";
      i_1++;
    }
    while(i_c > 0 && goto_unrolled_2[i_2] != goto_common[i_c - 1]){
      std::cout << "    [+] " << goto_unrolled_2[i_2] << "\n";
      i_2++;
    }
    std::cout << "    [v] " << goto_unrolled_2[i_2] << "\n";
    if (i_1 < size_1){
      i_1++;
    }
    i_2++;
    if (i_c > 0){
      i_c--;
    }
  }
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
  }

  std::vector<std::string > goto_common;

  if (size_1 != 0 && size_2 != 0){
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
    goto_common = goto_common_s[size_1][size_2];
  }
  unsigned size_c = goto_common.size();

  bool res = size_1 == size_2 && size_c == size_1 && size_c == size_2;

  if (!res)
  {
    do_diff(goto_unrolled_1, goto_unrolled_2, goto_common);
  }

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

  // stop iterating at the second function call (since the first one is "__CPROVER_initialize")
  for (unsigned i = functions.size() - 1; i > 0; i--)
  {
    std::cout << "checking \"" << (*functions[i].first) <<"\":..\n";

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

    std::cout << " --- " << (functions[i].second ? "" : "UN") << "preserved.\n";
    goto_unrolled_1.clear();
    goto_unrolled_2.clear();
  }
  after=current_time();
  std::cout << "    PROCESSING Time: " << time2string(after-before) << " sec.\n";
}
