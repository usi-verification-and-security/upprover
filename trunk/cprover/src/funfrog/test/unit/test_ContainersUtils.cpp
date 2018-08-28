//
// Created by Martin Blicha on 23.08.18.
//

#include <gtest/gtest.h>
#include <utils/containers_utils.h>

#include <set>

TEST(Contains_test, test_Set)
{
    std::set<int> s;
    ASSERT_FALSE(contains(s, 0));
    ASSERT_FALSE(contains(s, 1));
    s.insert(1);
    ASSERT_FALSE(contains(s, 0));
    ASSERT_TRUE(contains(s, 1));
    s.insert(2);
    ASSERT_FALSE(contains(s, 0));
    ASSERT_TRUE(contains(s, 1));
    ASSERT_TRUE(contains(s, 2));
}

