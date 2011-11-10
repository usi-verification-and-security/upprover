/*******************************************************************

 Module: Diff utility for 2 goto-binaries

 Author: Grigory Fedyukovich

\*******************************************************************/

#include "diff.h"

#define DEBUG_DIFF

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
    } else if (expr.type().id()==ID_bool){
      return (expr.is_true() ? "true" : "false");
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
  } else if(expr.id()==ID_sideeffect){
    if (expr.get(ID_statement)==ID_function_call){
      return expr.op0().to_string();
    }
    else {
      return expr.get("statement").as_string();
    }
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
      case GOTO:  {
        goto_programt::targetst::const_iterator it2 = it->targets.begin();
        unsigned tgt_location = (*it2)->location_number;

          res = "if (" + form(it->guard) + ") goto " + integer2string(tgt_location);
          // FIXME: change the absolute target location to relative one
        } break;
      case ASSUME:   { res = "assume (" + form(it->guard) + ")"; } break;
      case ASSERT:  { res = "assert (" + form(it->guard) + ")"; }  break;
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
        break;
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
  return /*integer2string(it->location_number) + ": " +*/ res;
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


bool difft :: is_untouched(const irep_idt &name)
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

bool difft :: unroll_goto(goto_functionst &goto_functions, const irep_idt &name,
      std::vector<std::pair<std::string, unsigned> > &goto_unrolled, unsigned init, bool inherit_change)
{
//  if (!is_untouched (name)){
//    return false;
//  }

  unsigned loc = init;
  const goto_programt& program = goto_functions.function_map[name].body;
  for(goto_programt::const_targett it = program.instructions.begin();
      it!=program.instructions.end(); ++it)
  {
    unsigned tmp = 0;
    if(it->type == FUNCTION_CALL){
      loc++;
      tmp = loc;
      if(inherit_change){
        const code_function_callt &call =
          to_code_function_call(to_code(it->code));

        const irep_idt &name_child = call.function().get("identifier");

        if (!is_untouched(name_child)){
          return false;   // the nested function was modified => this function is also modified
        }
      }
    }
    goto_unrolled.push_back(std::make_pair(cmd_str(it), tmp));
  }
  return true;
}

void copy(std::vector<std::pair<std::string, unsigned> > &goto_1,
    std::vector<std::pair<std::string, unsigned> > &goto_2){
  for (unsigned i = 0; i < goto_2.size(); i++){
    goto_1.push_back(goto_2[i]);
  }
}

bool compare_str_vecs(std::vector<std::pair<std::string, unsigned> > &goto_unrolled_1,
                      std::vector<std::pair<std::string, unsigned> > &goto_unrolled_2,
                      std::vector<std::pair<std::string, unsigned> > &goto_common){
  unsigned size_1 = goto_unrolled_1.size();
  unsigned size_2 = goto_unrolled_2.size();

  if (size_1 == 0 && size_2 == 0){
    return true;
  }

  if (size_1 != 0 && size_2 != 0){
    std::vector<std::pair<std::string, unsigned> > **goto_common_s =
        new std::vector<std::pair<std::string, unsigned> >*[size_1 + 1];
    for (unsigned i = 0; i <= size_1; ++i){
      goto_common_s[i] = new std::vector<std::pair<std::string, unsigned> >[size_2 + 1];
    }
    for (unsigned i = 1; i <= size_1; i++){
      for (unsigned j = 1; j <= size_2; j++){
        std::vector<std::pair<std::string, unsigned> >& tmp_i_j = goto_common_s[i][j];
        if (goto_unrolled_1[i-1].first == goto_unrolled_2[j-1].first){
          tmp_i_j.push_back(goto_unrolled_1[i-1]);
          copy(tmp_i_j, goto_common_s[i-1][j-1]);
        } else {
          std::vector<std::pair<std::string, unsigned> >& tmp_i_1_j = goto_common_s[i-1][j];
          std::vector<std::pair<std::string, unsigned> >& tmp_i_j_1 = goto_common_s[i][j-1];

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

  return res;
}

void difft :: do_proper_diff(std::vector<std::pair<std::string, unsigned> > &goto_unrolled_1,
             std::vector<std::pair<std::string, unsigned> > &goto_unrolled_2,
             std::vector<std::pair<std::string, unsigned> > &goto_common)
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
    while(i_c >= 0 && goto_unrolled_2[i_2].first != goto_common[i_c - 1].first){
#     ifdef DEBUG_DIFF
      std::cout << "    [+] " << goto_unrolled_2[i_2].first << "\n";
#     endif
      i_2++;

    }
    while(i_1 < size_1 && i_c >= 0 && goto_unrolled_1[i_1].first != goto_common[i_c - 1].first){
#     ifdef DEBUG_DIFF
      std::cout << "    [-] " << goto_unrolled_1[i_1].first << "\n";
#     endif
      i_1++;
    }
#   ifdef DEBUG_DIFF
    std::cout << "    [v] " << goto_unrolled_1[i_1].first << "\n";
#   endif

    if (do_write && goto_unrolled_1[i_1].second > 0){
      summs[goto_unrolled_1[i_1].second * 7 + 4] = "1";
    }

    if (i_1 < size_1){
      i_1++;
    }
    i_2++;
    if (i_c > 0){
      i_c--;
    }
  }
}

//void write_change(const irep_idt &name, std::vector<std::string > &summs)
//{
//  for (unsigned i = 0; i < summs.size(); i = i + 6){
//    if (summs[i] == name.as_string()){
//      summs[i+3] = "1";
//    }
//  }
//}


bool difft :: do_diff()
{
  if (do_write){
    // Load substituting scenario
    std::ifstream in;
    in.open(output);
    while (!in.eof()){
      std::string str;
      in >> str;
      summs.push_back(str);
    }
    in.close();
  }

  collect_functions(goto_functions_1, goto_functions_1.function_map["main"].body, functions);

  std::vector<std::pair<std::string, unsigned> > goto_unrolled_1;
  std::vector<std::pair<std::string, unsigned> > goto_unrolled_2;
  std::vector<std::pair<std::string, unsigned> > goto_common;

  // stop iterating at the second function call (since the first one is "__CPROVER_initialize")
  for (unsigned i = 1; i < functions.size(); i++)
  {
    std::cout << "checking \"" << (*functions[i].first) <<"\":..\n";

    bool pre_res_1 = unroll_goto(goto_functions_1, (*functions[i].first), goto_unrolled_1, i, false);
    bool pre_res_2 = unroll_goto(goto_functions_2, (*functions[i].first), goto_unrolled_2, i, false);

    bool pre_res_3 = false;
    if (pre_res_1 && pre_res_2){
      if (compare_str_vecs (goto_unrolled_1, goto_unrolled_2, goto_common)){
        pre_res_3 = true;
      }
    }

    if (pre_res_3 == false){
      functions[i].second = false;
      do_proper_diff(goto_unrolled_1, goto_unrolled_2, goto_common);
    } else if (summs.size() > i*7+3) {
      summs[i*7+3] = "1";
    }

    std::cout << " --- " << (functions[i].second ? "" : "UN") << "preserved.\n";
    goto_unrolled_1.clear();
    goto_unrolled_2.clear();
    goto_common.clear();
  }

  if (do_write){
    std::ofstream out;
    out.open(output);
    for (unsigned i = 0; i < summs.size(); i++){
      out << summs[i] << std::endl;
    }
    out.close();
  }

  bool res = true;
  for (unsigned i = 1; i < functions.size(); i++){
    res &= functions[i].second;
  }
  return res;
}
