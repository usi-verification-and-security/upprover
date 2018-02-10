//
// Created by Martin Blicha on 22.11.17.
//

#ifndef HIFROG_PARTITION_FWD_H
#define HIFROG_PARTITION_FWD_H

#include <list>
#include <util/irep.h>

class partitiont;

typedef int partition_idt;
typedef std::list<partition_idt> partition_idst;
typedef std::map<irep_idt, partition_idt> partition_mapt;
typedef std::list<unsigned> partition_locst;
typedef std::vector<partitiont> partitionst;

#endif //HIFROG_PARTITION_FWD_H
