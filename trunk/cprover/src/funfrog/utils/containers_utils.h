//
// Created by Martin Blicha on 23.08.18.
//

#ifndef PROJECT_CONTAINERS_UTILS_H
#define PROJECT_CONTAINERS_UTILS_H

#include <algorithm>

template<typename Cont, typename Elem>
bool contains(const Cont & container, const Elem& elem)
{
    return std::find(container.begin(), container.end(), elem) != container.end();
}

#endif //PROJECT_CONTAINERS_UTILS_H
