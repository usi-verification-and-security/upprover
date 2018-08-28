//
// Created by Martin Blicha on 12.07.18.
//

#ifndef PROJECT_UNIONFIND_H
#define PROJECT_UNIONFIND_H

#include <map>
#include "containers_utils.h"

template< typename Elem>
class UnionFind {
public:
    void makeSet(Elem x){
        assert(!contains(parent, x));
        parent[x] = x;
        rank[x] = 0;
    }

    // using path compression
    Elem find(Elem x){
        Elem old = x;
        Elem ancestor = parent[x];
        while (ancestor != x) {
            x = ancestor;
            ancestor = parent[x];
        }
        x = parent[old];
        while (ancestor != x) {
            parent[old] = ancestor;
            old = x;
            x = parent[old];
        }
        return ancestor;
    }

    void merge(Elem x, Elem y){
        auto xRoot = find(x);
        auto yRoot = find(y);

        // x and y are already in the same set
        if(xRoot == yRoot) return;

        // x and y are not in the same set, so we merge them
        if(rank[x] < rank[y]){
            std::swap(x,y);
        }
        parent[yRoot] = xRoot;
        if(rank[xRoot] == rank[yRoot]){
            ++rank[xRoot];
        }

    }

private:
    std::map<Elem, Elem> parent;
    std::map<Elem, std::size_t> rank;
};


#endif //PROJECT_UNIONFIND_H
