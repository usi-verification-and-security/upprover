/*******************************************************************

 Module: Diff utility for 2 goto-binaries

 This class was adapted from old SAT-based evolcheck developed by G. Fedyukovich

\*******************************************************************/
//#include <term_entry.h>
#include "diff.h"

//#define DEBUG_DIFF

/*******************************************************************\
 Purpose:
\*******************************************************************/
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
    } else if(expr.id()==ID_side_effect){
        if (expr.get(ID_statement)==ID_function_call){
            return form(expr.op0());//.to_string();
        }
        else {
            return expr.get_string("statement");//.as_string();
        }
    }
    return "(not supported yet: "+expr.id_string()+")";
}
/*******************************************************************\
 Purpose:
\*******************************************************************/
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
/*******************************************************************\
 
 Function:

 Purpose: simulates the behavior of existing code that tries to update new_sums based on old_sums
 
\*******************************************************************/
void difft :: stub_new_summs(unsigned loc){
    if (loc != 0){
        callhistory_new.push_back("__CPROVER_initialize");  //later an actual function name is pushed
        callhistory_new.push_back(integer2string(loc)); // wrong, but working
        callhistory_new.push_back("2");   //INLINE
        callhistory_new.push_back("0");   //Is_preserved_node?
        callhistory_new.push_back("1");   //Is_preserved_edge?    SA: Where is it useful?
        callhistory_new.push_back("0");   //has assertion in subtree
        callhistory_new.push_back("-");  //later a proper used_summaries will be pushed
    }
    std::vector <unsigned> calls = calltree_new[loc];
    for (unsigned i = 0; i < calls.size(); i++){
        stub_new_summs(calls[i]);
    }
}
/*******************************************************************\
Purpose: Performs a DFS traversal on FUNCTION_CALLs. Starts from entry point of program (main)
and recursively collects functions calls into vector called "functions"
It also relates function IDs to number of childeren;
fills two member fileds of difft class, namely functions_old, functions_new
by populating &functions
//This method builds some kind of call-tree with just numbers,
 it does not contain complete info as call_tree_nodet does  !
\*******************************************************************/
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
            functions.push_back(std::make_pair(&name, false));    //false as a default; is_touched?
            
            goto_functionst::function_mapt::const_iterator f_it =      //finds
                    goto_functions.function_map.find(name);
            
            if(f_it!=goto_functions.function_map.end())
            {   //Found
                collect_functions(goto_functions, f_it->second.body, functions, calltree, global_loc);
            }
        }
    }
    
    calltree[initial_loc] = current_children;    // if no FUNCTION_CALL is detected in subtree, the default
                                                // value of vector (empty) will be pushed
}

/*******************************************************************\
 
 Function:

 Purpose:

\*******************************************************************/
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
/*******************************************************************\
 
 Function:

 Purpose: TODO:SA: find a better name; it seems this func does not have anything to do with unrolling

\*******************************************************************/
bool difft :: add_loc_info(const goto_functionst &goto_functions, const irep_idt &name,
                           goto_sequencet &goto_unrolled,
                           std::map<unsigned,std::vector<unsigned> > &calltree, unsigned init, bool inherit_change)
{
//  if (!is_untouched (name)){
//    return false;
//  }
    
    unsigned loc = 0;
    const goto_programt& program = goto_functions.function_map.at(name).body;
    for(goto_programt::const_targett it = program.instructions.begin();
        it!=program.instructions.end(); ++it)
    {
        unsigned tmp = 0;
        if(it->type == FUNCTION_CALL){
            tmp = (calltree[init + 1])[loc];
            if(inherit_change){ //for now it never enters inside the If stat
                const code_function_callt &call =
                        to_code_function_call(to_code(it->code));
                
                const irep_idt &name_child = call.function().get("identifier");
                
                if (!is_untouched(name_child)){
                    return false;   // the nested function was modified => this function is also modified TODO refactor it.
                }
            } // end of if
            loc++;
        }
        //adding location info to diff
        goto_unrolled.push_back(triple<std::string, unsigned, const source_locationt*>(cmd_str(it), tmp, &(it->source_location)));
    }
    return true; // it seems always returns true //TODO refactor it.
}
/*******************************************************************\
 Purpose:
\*******************************************************************/
void copy(goto_sequencet &goto_1,
          goto_sequencet &goto_2){
    for (unsigned i = 0; i < goto_2.size(); i++){
        goto_1.push_back(goto_2[i]);
    }
}
/*******************************************************************\
 Purpose: if the new and old functions are the same returns true, size_1 == size_2 == size_c
 Note:SA: TODO: needs a major improvement/change.
          TODO: release the alocated memory 2-D array
\*******************************************************************/
bool compare_str_vecs(goto_sequencet &goto_unrolled_1,
                      goto_sequencet &goto_unrolled_2,
                      goto_sequencet &goto_common){
    unsigned size_1 = goto_unrolled_1.size();
    unsigned size_2 = goto_unrolled_2.size();
    
    if (size_1 == 0 && size_2 == 0){
        return true;                //nondet it holds
    }
    
    if (size_1 != 0 && size_2 != 0){
        goto_sequencet **goto_common_s =                //SA: here the pointer to pointer provides 2-D array
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
/*******************************************************************\
 
 Function:

 Purpose:

\*******************************************************************/
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
        while(goto_unrolled_2[i_2].first != goto_common[i_c - 1].first){   //goto_common filled in opposite direction
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
                    callhistory_new[(goto_unrolled_2[i_2].second - 1) * 7 + 4] = "0";
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
    } //End of while loop i_c>0
    
////XML output for diff
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
/*******************************************************************\
 Function:
 Purpose: If the new name is alreday present in the old version & if it's not already processed(visited),
 It gives each time a new ID for the functions of new version that matches with the old version.
 If the same function is called twice we give two different ID.
 Otherwise, if a new function name(perhaps renaming) pops out in the new version that was not in the old version we return -1;
Remark: the order of function calls matters here. DFS order.
\*******************************************************************/
int difft::get_call_tree_node_id(const irep_idt& new_call_name, std::vector<std::pair<const irep_idt*, bool> >& func_old, unsigned old){
    //ToDo: create more sophisticated method
//  if ((*functions[old].first) == new_call_name){
//    locs_visited.insert(old_loc);
//    return old;}
    for (unsigned i = 0; i < func_old.size(); i++){
        //checks if the new name is alreday present in the old version & if it's not already processed(visited)
        if ((*func_old[i].first) == new_call_name && locs_visited.find(i) == locs_visited.end()){  //locs_visted keeps i to ensure
                                                                                                        //the next time to give a new i
            locs_visited.insert(i);
            return i;
        }
    }
    return -1; //means there is a new function name(perhaps renaming) that was not in the old version.
}
/*******************************************************************\
 
 Function:

 Purpose:

\*******************************************************************/
bool difft :: do_diff (const goto_functionst &goto_functions_1 , const goto_functionst &goto_functions_2)
{
    //naming helpers for omega file enteries
    const int ENTRIES_PER_NODE = 7; //ENTRIES_PER_FUNCTION in omega file
    const int FUNCTION_NAME = 0;
    const int CALL_LOCATION = 1;
    const int NODE_REPRESENTATION = 2; //function precision
    const int PRESERVED_NODE = 3;
    const int PRESERVED_EDGE = 4;
    const int ASSERT_IN_SUBTREE = 5;
  //  const int USED_SUMMARIES = 6; //fo r e.g,in ex21-*.c summary in minus2 should be removed later
    
    if (do_write){   // will write on __omega file later on
        // Load substituting scenario
        std::ifstream in;
        in.open(input);
        while (!in.eof()){
            std::string str;
            in >> str;
            callhistory_old.push_back(str);   // contains all __omega as vec of string
        }
        in.close();
    }
    
    if (locs_output){
        std::cout << "<cprover>" << std::endl;
    }
    
    unsigned loc = 0;
    collect_functions(goto_functions_1, goto_functions_1.function_map.at(goto_functionst::entry_point()).body, functions_old, calltree_old, loc);
    loc = 0;
    collect_functions(goto_functions_2, goto_functions_2.function_map.at(goto_functionst::entry_point()).body, functions_new, calltree_new, loc);
    
    if (do_write){
        stub_new_summs(0);
    }
    
    goto_sequencet goto_unrolled_1;
    goto_sequencet goto_unrolled_2;
    goto_sequencet goto_common;
    
    symbol_tablet temp_symb;
    namespacet ns (temp_symb);
    
    for (unsigned i = 0; i < functions_new.size() ; i++)
    {
        bool pre_comp_res = false;
        
        const irep_idt& new_call_name = (*functions_new[i].first);
        std::string call_newname = new_call_name.c_str();
        
        unsigned old_call_tree_node_id = get_call_tree_node_id(new_call_name, functions_old, i);
        bool is_new_node = (old_call_tree_node_id == -1);
        if (do_write){
            if (!is_new_node){     //if locs already has been visited it is -1
                for (unsigned j = 0; j < ENTRIES_PER_NODE; j++){
                    if (j != PRESERVED_EDGE)
                        //when j=6 used_summaries are copied
                        callhistory_new[i * ENTRIES_PER_NODE + j] = callhistory_old[old_call_tree_node_id * ENTRIES_PER_NODE + j];
                }  // End of Forloop j
            } else {
                callhistory_new[i * ENTRIES_PER_NODE + FUNCTION_NAME] = new_call_name.c_str(); // new function name, so add it manually
            }
        }
        //interface change support: if the signature of a function was changed, we mark it as changed,
        // and invalidate all summaries(mark as Inline); so the upgrade checking algorithm starts with the parent)
        if(is_new_node || (!base_type_eq(goto_functions_1.function_map.at(new_call_name).type,
                                         goto_functions_2.function_map.at(new_call_name).type, ns) && !locs_output)){
            msg.status() << std::string("function \"") + new_call_name.c_str() + std::string ("\" has changed interface") << msg.eom;
            //manually add omega entries for new name that were not in old goto-function (goto_functions_1)
            callhistory_new[i * ENTRIES_PER_NODE + CALL_LOCATION] = "-1"; // TODO: What to put here for new function not present in old version
            callhistory_new[i * ENTRIES_PER_NODE + NODE_REPRESENTATION] = "2";  //Set INLINE for the interface change or new name
            callhistory_new[i * ENTRIES_PER_NODE + PRESERVED_NODE] = "0";
            callhistory_new[i * ENTRIES_PER_NODE + PRESERVED_EDGE] = "0";
            callhistory_new[i * ENTRIES_PER_NODE + ASSERT_IN_SUBTREE] = "0"; // TODO: FIGURE out if this we need to find out the right value
            //callhistory_new[i * ENTRIES_PER_NODE + USED_SUMMARIES] = "-";
            continue;// in this case we stop processing this node here! Dont check goto_functions_1 as does not exist in the old version-->Crash
        }
        
        if (i == 0){// it is on __CPROVER_initialize
             pre_comp_res = true;
        }
       else {
            bool pre_res_1 = add_loc_info(goto_functions_1, new_call_name, goto_unrolled_1,
                                          calltree_old, old_call_tree_node_id, false);
            
            bool pre_res_2 = add_loc_info(goto_functions_2, new_call_name, goto_unrolled_2,
                                          calltree_new, i, false);
            //TODO currentlyadd_loc_info is always return true; it just updates call-locations. Simplify it!
            
            if (pre_res_1 && pre_res_2){
                //when node has changed, it should return false
                pre_comp_res = compare_str_vecs (goto_unrolled_1, goto_unrolled_2, goto_common);
            }
      }
        functions_new[i].second = pre_comp_res;
        //if initial comparision failed, lets do a proper diff
        if (pre_comp_res == false){
            do_proper_diff(goto_unrolled_1, goto_unrolled_2, goto_common);
            if (do_write) {
                callhistory_new[i * ENTRIES_PER_NODE + PRESERVED_NODE] = "0";   //function has changed
            }
        }
        else {
            if (do_write) {
                callhistory_new[i * ENTRIES_PER_NODE + PRESERVED_NODE] = "1";   //it is a preserved_node
            }
        }
        //report
        if (!locs_output)
            msg.status() << std::string("function \"") + new_call_name.c_str() + std::string ("\" is ") +
                            (functions_new[i].second ? std::string("") : std::string("UN")) + std::string("preserved") +
                            (functions_new[i].second ? std::string("") : std::string(" (") +
                             std::to_string(goto_unrolled_1.size() - goto_common.size() + goto_unrolled_2.size() - goto_common.size())//all-assert cmdline
                                                                 + std::string(")")) <<msg.eom;
        goto_unrolled_1.clear();
        goto_unrolled_2.clear();
        goto_common.clear();
    }   // End of Forloop over functions_new.size
    
    //after Make diff & Construct changed call_tree_node  -> writes back to "__omega"
    if (do_write){
        std::ofstream out;
        out.open(output);    //if you don't provide a new file it will overwrite the old __omega file.
        for (unsigned i = 0; i < callhistory_new.size(); i++){
            out << callhistory_new[i] << std::endl;
        }
        out.close();
    }
    
    if (locs_output){
        std::cout << "</cprover>" << std::endl;
    }
    
    bool res = true;
    for (unsigned i = 1; i < functions_old.size(); i++){
        res &= functions_new[i].second;     // continues Bit Wise AND for all the functions' res
    }                                       //if false, at least one function has changed
    return res;
}