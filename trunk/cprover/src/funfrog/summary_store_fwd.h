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
class smt_itp_z3t;

typedef std::size_t summary_idt;
typedef std::vector<summary_idt> summary_ids_vect;
typedef std::unordered_set<summary_idt> summary_ids_sett;
typedef itpt itpt_summaryt;
typedef prop_itpt prop_summaryt;
typedef smt_itpt smt_itpt_summaryt;
typedef smt_itp_z3t smt_summary_z3t;

class summary_storet;

#endif //HIFROG_SUMMARY_STORE_FWD_H
