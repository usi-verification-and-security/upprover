//
// Created by Martin Blicha on 23.08.18.
//

#ifndef PROJECT_CONTAINERS_UTILS_H
#define PROJECT_CONTAINERS_UTILS_H

#include <algorithm>
#include <map>
#include <set>

template<typename Cont, typename Elem>
bool contains(const Cont & container, const Elem& elem)
{
    return std::find(container.begin(), container.end(), elem) != container.end();
}

template <typename Elem, typename... Ts>
bool contains(const std::map<Ts...>& c, const Elem& x)
{
    return c.find(x) != std::end(c);
}

template <typename Elem, typename... Ts>
bool contains(const std::set<Ts...>& c, const Elem& x)
{
    return c.find(x) != std::end(c);
}

#endif //PROJECT_CONTAINERS_UTILS_H
