//
// Created by Martin Blicha on 24.07.18.
//

#include <gtest/gtest.h>
#include <funfrog/solvers/prop_itp.h>
#include <fstream>

bool operator==(prop_itpt const & itp1, prop_itpt const & itp2 ){
    if(itp1.get_clauses().size() != itp2.get_clauses().size()){
        return false;
    }
    for(int i = 0; i < itp1.get_clauses().size(); ++i){
        if(itp1.get_clauses()[i] != itp2.get_clauses()[i]){
            return false;
        }
    }
    return true;
}

TEST(test_Ser_Deser, test_Ser_Deser_Equal)
{
    prop_itpt sum;
    sum.set_no_variables(2);
    sum.set_no_original_variables(2);
    sum.lor(literalt(1, false), literalt(1,true));
    ASSERT_EQ(sum.get_clauses().size(), 3);
    std::stringstream ss;
    sum.serialize(ss);
    prop_itpt deser;
    deser.deserialize(ss);
    ASSERT_EQ(deser.get_clauses().size(), 3);
    ASSERT_EQ(sum, deser);

}