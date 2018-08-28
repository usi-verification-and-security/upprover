//
// Created by Martin Blicha on 15.08.18.
//

#include "partition_iface.h"

std::vector<symbol_exprt> partition_ifacet::get_iface_symbols() const {
    std::vector<symbol_exprt> iface_symbols;
    iface_symbols.reserve(this->argument_symbols.size() +
                           this->out_arg_symbols.size()+4);
    iface_symbols = this->argument_symbols; // Add SSA instances of funcs
    iface_symbols.insert(iface_symbols.end(),
                          this->out_arg_symbols.begin(),
                          this->out_arg_symbols.end()); // Add globals
    iface_symbols.push_back(this->callstart_symbol);
    iface_symbols.push_back(this->callend_symbol);
    if (this->assertion_in_subtree) {
        iface_symbols.push_back(this->error_symbol);
    }
    if (this->returns_value) {
        iface_symbols.push_back(this->retval_symbol);
    }
    return iface_symbols;
}