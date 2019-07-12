//
// Created by Martin Blicha on 14.08.18.
//

#include <gtest/gtest.h>
#include <funfrog/summary_store.h>
#include <funfrog/smt_summary_store.h>
#include <funfrog/prop_summary_store.h>
#include <funfrog/solvers/smt_itp.h>
#include <funfrog/solvers/prop_itp.h>


TEST(test_Insert, test_Insert_Different){
    summary_storet* ss = new smt_summary_storet;
    smt_itpt* itp1 = new smt_itpt;
    itp1->setInterpolant(PTRef{1});
    std::string fun{"foo"};
    ss->insert_summary(itp1, fun);
    smt_itpt* itp2 = new smt_itpt;
    itp2->setInterpolant(PTRef{2});
    ss->insert_summary(itp2, fun);
    auto res = ss->get_summariesID(fun);
    ASSERT_EQ(res.size(), 2);
    delete ss;
}

TEST(test_Insert, test_Insert_Same){
    summary_storet* ss = new smt_summary_storet;
    smt_itpt* itp1 = new smt_itpt;
    itp1->setInterpolant(PTRef{1});
    std::string fun{"foo"};
    ss->insert_summary(itp1, fun);
    smt_itpt* itp2 = new smt_itpt;
    itp2->setInterpolant(PTRef{1});
    ss->insert_summary(itp2, fun);
    auto res = ss->get_summariesID(fun);
    ASSERT_EQ(res.size(), 1);
    delete ss;
}

TEST(test_Insert, test_Insert_Different_Prop){
    summary_storet* ss = new prop_summary_storet;
    auto itp1 = new prop_itpt;
    itp1->set_no_original_variables(2);
    itp1->set_no_variables(2);
    itp1->lor(literalt(1, false), literalt(1,true));
    std::string fun{"foo"};
    ss->insert_summary(itp1, fun);
    auto* itp2 = new prop_itpt;
    itp2->set_no_original_variables(2);
    itp2->set_no_variables(2);;
    itp2->set_root_literal(literalt{1,false});
    ss->insert_summary(itp2, fun);
    auto res = ss->get_summariesID(fun);
    ASSERT_EQ(res.size(), 2);
}


