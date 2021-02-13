//
// Created by Martin Blicha on 13.08.18.
//

#ifndef PROJECT_NAMING_BOOLBV_H
#define PROJECT_NAMING_BOOLBV_H

#include <solvers/flattening/bv_pointers.h>

class naming_boolbv :public bv_pointerst{
public:
    naming_boolbv(const namespacet &_ns, propt &_prop, message_handlert & message_handler) : bv_pointerst{_ns, _prop} {}
protected:
    bvt convert_symbol(const exprt & expr) override {
        auto res =  bv_pointerst::convert_symbol(expr);
        assert(res.size() == boolbv_width(expr.type()));
        auto name = id2string(expr.get(ID_identifier));
        for(std::size_t i = 0; i < res.size(); ++i){
            prop.set_variable_name(res[i], name + "_B" + std::to_string(i));
        }
        return res;
    }
};

#endif //PROJECT_NAMING_BOOLBV_H
