//
// Created by Martin Blicha on 03.11.17.
//

#ifndef HIFROG_PARTITION_IFACE_FWD_H
#define HIFROG_PARTITION_IFACE_FWD_H

#include <list>
#include <vector>
#include "summary_store_fwd.h"

class partition_ifacet;

typedef std::list<partition_ifacet*> partition_iface_ptrst;
typedef std::vector<std::pair<partition_ifacet*, summary_idt> > interpolant_mapt;

#endif //HIFROG_PARTITION_IFACE_FWD_H
