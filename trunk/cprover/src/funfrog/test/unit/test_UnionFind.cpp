#include <gtest/gtest.h>
#include <utils/UnionFind.h>
TEST(UnionFind_test, test_Different)
{
    UnionFind<int> uf;
    uf.makeSet(1);
    uf.makeSet(2);
    ASSERT_TRUE(uf.find(1) != uf.find(2));
}

TEST(UnionFind_test, test_Same)
{
    UnionFind<int> uf;
    uf.makeSet(1);
    uf.makeSet(2);
    uf.merge(1,2);
    ASSERT_EQ(uf.find(1), uf.find(2));
    uf.makeSet(3);
    uf.merge(3,2);
    ASSERT_EQ(uf.find(1), uf.find(3));
}
