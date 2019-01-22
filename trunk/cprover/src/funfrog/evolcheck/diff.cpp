/*******************************************************************

 Module: Diff utility for 2 goto-binaries

 This class was adapted from old SAT-based evolcheck developed by G. Fedyukovich

\*******************************************************************/
#include <i2string.h>
#include "diff.h"
#include <util/std_expr.h>

//#define DEBUG_DIFF

std::string form(const exprt &expr)
{
    if (expr.has_operands()){
        std::string res = expr.id_string();
        for (unsigned i = 0; i < expr.operands().size(); i++){
            res += res + " " + form(expr.operands()[i]);
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
        return expr.get_string("identifier");//.as_string();
    } else if(expr.id()==ID_sideeffect){
        if (expr.get(ID_statement)==ID_function_call){
            return form(expr.op0());//.to_string();
        }
        else {
            return expr.get_string("statement");//.as_string();
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
            //goto_programt::targetst::const_iterator it2 = it->targets.begin();
            //unsigned tgt_location = (*it2)->location_number;
            
            res = "if (" + form(it->guard) + ") goto " ;//+ integer2string(tgt_location);
            // FIXME: change the absolute target location to relative one
        } break;
        case ASSUME:   { res = "assume (" + form(it->guard) + ")"; } break;
        case ASSERT:  { res = "assert (" + form(it->guard) + ")"; }  break;
        case RETURN: {
            const code_returnt &ret = to_code_return(it->code);
            res = "return";
            if (ret.has_return_value()){
                res += " (" + form(ret.return_value()) + ")";
            }
        }
            break;
        case ASSIGN: {
            const code_assignt &ass =
                    to_code_assign(it->code);
            res = (ass.lhs().get_string("identifier") + " = " + form(ass.rhs()));
        }
            break;
        case FUNCTION_CALL: {
            const code_function_callt &call = to_code_function_call(to_code(it->code));
            res = call.lhs().get_string("identifier") + " = " + call.function().get_string("identifier") + "(";
            for (unsigned i = 0; i < call.arguments().size(); i++){
                res += " (" + form (call.arguments()[i]) + ")";
            }
            res += ")";
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
    return res;
}

void difft :: stub_new_summs(unsigned loc){
    if (loc != 0){
        new_summs.push_back("-");
        new_summs.push_back(integer2string(loc)); // wrong, but working
        new_summs.push_back("2");
        new_summs.push_back("0");
        new_summs.push_back("1");
        new_summs.push_back("0");
        new_summs.push_back("-");
    }
    std::vector <unsigned> calls = calltree_new[loc];
    for (unsigned i = 0; i < calls.size(); i++){
        stub_new_summs(calls[i]);
    }
}

void collect_functions(const goto_functionst &goto_functions, const goto_programt &program,
                       std::vector<std::pair<const irep_idt*, bool> > &functions,
                       std::map<unsigned, std::vector<unsigned> > &calltree, unsigned& global_loc)
{
    unsigned initial_loc = global_loc;
    std::vector<unsigned> current_children;
    
    for(goto_programt::const_targett it = program.instructions.begin();
        it!=program.instructions.end(); ++it)
    {
        if(it->type == FUNCTION_CALL)
        {
            global_loc++;
            const code_function_callt &call =
                    to_code_function_call(to_code(it->code));
            
            const irep_idt &name = call.function().get("identifier");
            
            current_children.push_back(global_loc);
            functions.push_back(std::make_pair(&name, false));
            
            goto_functionst::function_mapt::const_iterator f_it =
                    goto_functions.function_map.find(name);
            
            if(f_it!=goto_functions.function_map.end())
            {
                collect_functions(goto_functions, f_it->second.body, functions, calltree, global_loc);
            }
        }
    }
    calltree[initial_loc] = current_children;
}


bool difft :: is_untouched(const irep_idt &name)
{
    for (unsigned i = 0; i < functions_old.size(); i++){
        if ((*functions_old[i].first) == name){
            if (functions_old[i].second == false){
                return false;
            }
        }
    }
    return true;
}

bool difft :: unroll_goto(goto_functionst &goto_functions, const irep_idt &name,
                          goto_sequencet &goto_unrolled,
                          std::map<unsigned,std::vector<unsigned> > &calltree, unsigned init, bool inherit_change)
{
//  if (!is_untouched (name)){
//    return false;
//  }
    
    unsigned loc = 0;
    const goto_programt& program = goto_functions.function_map[name].body;
    for(goto_programt::const_targett it = program.instructions.begin();
        it!=program.instructions.end(); ++it)
    {
        unsigned tmp = 0;
        if(it->type == FUNCTION_CALL){
            tmp = (calltree[init + 1])[loc];
            if(inherit_change){
                const code_function_callt &call =
                        to_code_function_call(to_code(it->code));
                
                const irep_idt &name_child = call.function().get("identifier");
                
                if (!is_untouched(name_child)){
                    return false;   // the nested function was modified => this function is also modified
                }
            }
            loc++;
        }
        
        goto_unrolled.push_back(triple<std::string, unsigned, const locationt*>(cmd_str(it), tmp, &(it->location)));
    }
    return true;
}

void copy(goto_sequencet &goto_1,
          goto_sequencet &goto_2){
    for (unsigned i = 0; i < goto_2.size(); i++){
        goto_1.push_back(goto_2[i]);
    }
}

bool compare_str_vecs(goto_sequencet &goto_unrolled_1,
                      goto_sequencet &goto_unrolled_2,
                      goto_sequencet &goto_common){
    unsigned size_1 = goto_unrolled_1.size();
    unsigned size_2 = goto_unrolled_2.size();
    
    if (size_1 == 0 && size_2 == 0){
        return true;
    }
    
    if (size_1 != 0 && size_2 != 0){
        goto_sequencet **goto_common_s =
                new goto_sequencet*[size_1 + 1];
        for (unsigned i = 0; i <= size_1; ++i){
            goto_common_s[i] = new goto_sequencet[size_2 + 1];
        }
        for (unsigned i = 1; i <= size_1; i++){
            for (unsigned j = 1; j <= size_2; j++){
                goto_sequencet& tmp_i_j = goto_common_s[i][j];
                if (goto_unrolled_1[i-1].first == goto_unrolled_2[j-1].first){
                    tmp_i_j.push_back(goto_unrolled_1[i-1]);
                    copy(tmp_i_j, goto_common_s[i-1][j-1]);
                } else {
                    goto_sequencet& tmp_i_1_j = goto_common_s[i-1][j];
                    goto_sequencet& tmp_i_j_1 = goto_common_s[i][j-1];
                    
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

void difft :: do_proper_diff(goto_sequencet &goto_unrolled_1,
                             goto_sequencet &goto_unrolled_2,
                             goto_sequencet &goto_common)
{
    // sizes
    unsigned size_1 = goto_unrolled_1.size();
    unsigned size_2 = goto_unrolled_2.size();
    unsigned size_c = goto_common.size();
    
    // iterators
    unsigned i_1 = 0;
    unsigned i_2 = 0;
    unsigned i_c = size_c;
    
    while (i_c > 0){
#     ifdef DEBUG_DIFF
        std::cout << i_1 << " (" << size_1 << ") " <<i_2 << " (" << size_2 << ") " <<i_c << " (" << size_c << ")\n";
#     endif
        while(goto_unrolled_2[i_2].first != goto_common[i_c - 1].first){
#     ifdef DEBUG_DIFF
            std::cout << "    [+] " << goto_unrolled_2[i_2].first
          << " // " << (*goto_unrolled_2[i_2].third).as_string()
          << std::endl;
#     endif
            if (locs_output)
                std::cout << "<ADDED> " << std::endl <<
                          "  <file>" << (*goto_unrolled_2[i_2].third).get("file") << "</file>" << std::endl <<
                          "  <line>" << (*goto_unrolled_2[i_2].third).get("line") << "</line>" << std::endl <<
                          "</ADDED>" << std::endl;
            if (goto_unrolled_2[i_2].second > 0){
#     ifdef DEBUG_DIFF
                std::cout << " --- function call UNpreserved.\n";
#     endif
                if (do_write){
                    new_summs[(goto_unrolled_2[i_2].second-1) * 7 + 4] = "0";
                }
            }
            i_2++;
        }
        while(goto_unrolled_1[i_1].first != goto_common[i_c - 1].first){
#     ifdef DEBUG_DIFF
            std::cout << "    [-] " << goto_unrolled_1[i_1].first << "\n";
      if (goto_unrolled_1[i_1].second > 0){
        std::cout << " --- function call UNpreserved.\n";
      }
#     endif
            if (locs_output)
                //std::cout << "REMOVED: " << (*goto_unrolled_1[i_1].third).as_string() << std::endl;
                std::cout << "<REMOVED> " << std::endl <<
                          "  <file>" << (*goto_unrolled_2[0].third).get("file") << "</file>" << std::endl <<
                          "  <line>" << (*goto_unrolled_2[0].third).get("line") << "</line>" << std::endl <<
                          "</REMOVED>" << std::endl;
            i_1++;
        }
#   ifdef DEBUG_DIFF
        std::cout << "    [v] " << goto_unrolled_1[i_1].first << "\n";
#   endif

#   ifdef DEBUG_DIFF
        if (goto_unrolled_1[i_1].second > 0){
      std::cout << " --- function call preserved.\n";
    }
#   endif
        
        if (i_1 < size_1){
            i_1++;
        }
        if (i_2 < size_2){
            i_2++;
        }
        i_c--;
    }
    
    while (i_2 < size_2){
#   ifdef DEBUG_DIFF
        std::cout << i_1 << " (" << size_1 << ") " <<i_2 << " (" << size_2 << ") " <<i_c << " (" << size_c << ")\n";
    std::cout << "    [+] " << goto_unrolled_2[i_2].first << "\n";
#   endif
        if (locs_output)
            std::cout << "<ADDED> " << std::endl <<
                      "  <file>" << (*goto_unrolled_2[i_2].third).get("file") << "</file>" << std::endl <<
                      "  <line>" << (*goto_unrolled_2[i_2].third).get("line") << "</line>" << std::endl <<
                      "</ADDED>" << std::endl;
        i_2++;
    }
    
    while (i_1 < size_1){
#   ifdef DEBUG_DIFF
        std::cout << i_1 << " (" << size_1 << ") " <<i_2 << " (" << size_2 << ") " <<i_c << " (" << size_c << ")\n";
    std::cout << "    [-] " << goto_unrolled_1[i_1].first << "\n";
#   endif
        if (locs_output)
            //std::cout << "REMOVED: " << (*goto_unrolled_1[i_1].third).as_string() << std::endl;
            std::cout << "<REMOVED> " << std::endl <<
                      "  <file>" << (*goto_unrolled_2[0].third).get("file") << "</file>" << std::endl <<
                      "  <line>" << (*goto_unrolled_2[0].third).get("line") << "</line>" << std::endl <<
                      "</REMOVED>" << std::endl;
        i_1++;
    }
}

int difft :: get_call_loc(const irep_idt& name, std::vector<std::pair<const irep_idt*, bool> >& functions, unsigned old){
    //ToDo: create more sophisticated method
//  if ((*functions[old].first) == name){
//    locs_visited.insert(old_loc);
//    return old;
//  }
    
    for (unsigned i = 0; i < functions.size(); i++){
        if ((*functions[i].first) == name &&
            locs_visited.find(i) == locs_visited.end()){
            locs_visited.insert(i);
            return i;
        }
    }
    return -1;
}

bool difft :: do_diff()
{
    if (do_write){
        // Load substituting scenario
        std::ifstream in;
        in.open(input);
        while (!in.eof()){
            std::string str;
            in >> str;
            old_summs.push_back(str);
        }
        in.close();
    }
    
    if (locs_output){
        std::cout << "<cprover>" << std::endl;
    }
    
    unsigned loc = 0;
    collect_functions(goto_functions_1, goto_functions_1.function_map["main"].body, functions_old, calltree_old, loc);
    loc = 0;
    collect_functions(goto_functions_2, goto_functions_2.function_map["main"].body, functions_new, calltree_new, loc);
    
    if (do_write){
        stub_new_summs(0);
    }
    
    goto_sequencet goto_unrolled_1;
    goto_sequencet goto_unrolled_2;
    goto_sequencet goto_common;
    
    contextt temp_context;
    namespacet ns (temp_context);
    
    for (unsigned i = 0; i < functions_new.size(); i++)
    {
        bool pre_res_3 = false;
        
        const irep_idt& call_name = (*functions_new[i].first);
        
        unsigned call_loc = get_call_loc(call_name, functions_old, i);
        
        if (do_write){
            if (call_loc != -1){
                for (unsigned j = 0; j < 7; j++)
                    if (j != 4)
                        new_summs[i * 7 + j] = old_summs[call_loc * 7 + j];
            } else {
                new_summs[i * 7] = call_name.c_str();
            }
        }
        
        if(!base_type_eq(goto_functions_1.function_map[call_name].type,
                         goto_functions_2.function_map[call_name].type, ns) && !locs_output){
            status (std::string("function \"") + call_name.c_str() + std::string ("\" has changed interface"));
            new_summs[i * 7 + 2] = "2";
            continue;
        }
        
        if (i == 0){
            pre_res_3 = true;
        } else { // dirty hack for __CPROVER_initialize (sometimes it exceeds memory, but never is changed)
            bool pre_res_1 = unroll_goto(goto_functions_1, call_name, goto_unrolled_1,
                                         calltree_old, call_loc, false);
            
            bool pre_res_2 = unroll_goto(goto_functions_2, call_name, goto_unrolled_2,
                                         calltree_new, i, false);
            
            if (pre_res_1 && pre_res_2){
                if (compare_str_vecs (goto_unrolled_1, goto_unrolled_2, goto_common)){
                    pre_res_3 = true;
                }
            }
        }
        functions_new[i].second = pre_res_3;
        if (pre_res_3 == false){
            do_proper_diff(goto_unrolled_1, goto_unrolled_2, goto_common);
            if (do_write) {
                new_summs[i*7 + 3] = "0";
            }
        } else {
            if (do_write) {
                new_summs[i*7 + 3] = "1";
            }
        }
        if (!locs_output)
            status (std::string("function \"") + call_name.c_str() + std::string ("\" is ") +
                    (functions_new[i].second ? std::string("") : std::string("UN")) + std::string("preserved") +
                    (functions_new[i].second ? std::string("") : std::string(" (") +
                                                                 i2string(goto_unrolled_1.size() - goto_common.size() + goto_unrolled_2.size() - goto_common.size())
                                                                 + std::string(")")));
        goto_unrolled_1.clear();
        goto_unrolled_2.clear();
        goto_common.clear();
    }
    
    if (do_write){
        std::ofstream out;
        out.open(output);
        for (unsigned i = 0; i < new_summs.size(); i++){
            out << new_summs[i] << std::endl;
        }
        out.close();
    }
    
    if (locs_output){
        std::cout << "</cprover>" << std::endl;
    }
    
    bool res = true;
    for (unsigned i = 1; i < functions_old.size(); i++){
        res &= functions_new[i].second;
    }
    return res;
}

