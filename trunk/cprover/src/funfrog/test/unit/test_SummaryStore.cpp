//
// Created by Martin Blicha on 14.08.18.
//

#include <gtest/gtest.h>
#include <funfrog/summary_store.h>
#include <funfrog/smt_summary_store.h>
#include <funfrog/prop_summary_store.h>
#include <funfrog/solvers/smt_itp.h>
#include <funfrog/solvers/prop_itp.h>
#include <funfrog/solvers/solver_options.h>
#include <funfrog/solvers/smtcheck_opensmt2_lra.h>
#include <fstream>
#include <string>

TEST(test_Insert, test_Insert_Different){
    summary_storet* ss = new smt_summary_storet;
    smt_itpt* itp1 = new smt_itpt;
    itp1->setInterpolant(PTRef{1});
    std::string fun{"foo"};
    ss->insert_summary(itp1, fun);
    smt_itpt* itp2 = new smt_itpt;
    itp2->setInterpolant(PTRef{2});
    ss->insert_summary(itp2, fun);
    auto res = ss->get_summaries(fun);
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
    auto res = ss->get_summaries(fun);
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
    auto res = ss->get_summaries(fun);
    ASSERT_EQ(res.size(), 2);
}


//In this test we check when a given summary is serialized to a FILE, and then in the second run
// gets deserialized from the FILE, the summaryID remains the same.
TEST(test_IDequality, test_IDequality_serialize_deserialize_lra) {

    solver_optionst sop;
    smtcheck_opensmt2t* decider1 = new smtcheck_opensmt2t_lra(sop, "lra checker");
    smt_summary_storet * store1 = new smt_summary_storet(decider1);

//    auto lra_solver_ptr = std::unique_ptr<smtcheck_opensmt2t_lra>{new smtcheck_opensmt2t_lra(solver_options, "lra checker")};
//    smtcheck_opensmt2t_lra* lra_solver1 = new smtcheck_opensmt2t_lra(solver_options, "lra checker");  //raw
//    auto & lra_solver = *lra_solver_ptr;

    smt_itpt* itp1 = new smt_itpt;
    itp1->setInterpolant(PTRef{1});
    std::string fun{"foo"};
    store1->insert_summary(itp1, fun);
//  auto sum_ID1 = store1->get_summaries(fun)[0];

    itp1->setDecider(decider1);   //? Is it needed?
    const std::string& summary_file = "__summaries";  //file goes to build/bin/
    if (!summary_file.empty()) {
    std::ofstream out;
    out.open(summary_file.c_str());
    store1->serialize(out);    //hits assert in Alloc.h in OpenSMT
    out.close();
    }

    delete store1;
    delete decider1;

//create again(simulates 2nd run)
    smtcheck_opensmt2t* decider2 = new smtcheck_opensmt2t_lra(sop, "lra checker");
    smt_summary_storet * store2 = new smt_summary_storet(decider2);

    std::vector <std::string> summary_files;
    summary_files.push_back(summary_file);

    if (!summary_files.empty()) {
        store2->deserialize(summary_files);
    }
    auto sum_ID2 = store2->get_summaries(fun)[0];
//  check if  they are equal(sum_ID1, sum_ID2):
    auto res = store2->find_summary(sum_ID2).equals(itp1);
    ASSERT_TRUE(res);
}

