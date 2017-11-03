//
// Created by Martin Blicha on 03.11.17.
//

#ifndef HIFROG_SUMMARY_STORE_FWD_H
#define HIFROG_SUMMARY_STORE_FWD_H

#include <vector>
#include <unordered_set>

class itpt;
class prop_itpt;
class smt_itpt;
class function_infot;

typedef long unsigned summary_idt;
typedef std::vector<summary_idt> summary_idst;
typedef std::unordered_set<summary_idt> summary_ids_sett;
typedef itpt summaryt;
typedef prop_itpt prop_summaryt;
typedef smt_itpt smt_summaryt;
typedef std::unordered_map<irep_idt, function_infot, irep_id_hash> function_infost;

class summary_storet;

#endif //HIFROG_SUMMARY_STORE_FWD_H
