// Created on 2019-07-11

#include <gtest/gtest.h>
#include <funfrog/summary_store.h>
#include <funfrog/smt_summary_store.h>
#include <funfrog/prop_summary_store.h>
#include <funfrog/solvers/smt_itp.h>
#include <funfrog/solvers/prop_itp.h>
#include <funfrog/solvers/solver_options.h>
#include <funfrog/solvers/smtcheck_opensmt2_lra.h>
#include <funfrog/solvers/smtcheck_opensmt2_uf.h>
#include <fstream>
#include <string>
#include <funfrog/partition_iface.h>
#include <funfrog/call_tree_node.h>

//This test checks when a given summary is serialized to a FILE, and then in the second run
// gets deserialized from the same FILE, the summaryID remains the same.

TEST(test_IDequality, test_IDequality_serialize_deserialize_lra) {

    solver_optionst sop;
    smtcheck_opensmt2t* decider1 = new smtcheck_opensmt2t_lra(sop, "lra checker");
    smt_summary_storet * store1 = new smt_summary_storet(decider1);

    std::string fun{"foo"};
    std::vector<symbol_exprt> iface_symbols;
    summary_idt sum_ID1;
    {
       //create ITP
        auto * stub = decider1->create_stub_summary(fun);   //stub (type itpt*) points to a dynamicly allocated obj
       //generalize ITP
        decider1->generalize_summary(stub, iface_symbols);
       //store ITP
        sum_ID1 = store1->insert_summary(stub, fun);
       // Don't use stub after this point
    }
    // insert_summary passes the ownership to summary_store, don't use the pointer anymore
    const std::string& summary_file = "__summaries";  //file goes to build/bin/
    if (!summary_file.empty()) {
    std::ofstream out;
    out.open(summary_file.c_str());
    store1->serialize(out);
    out.close();
    }
    delete decider1;

//create again(simulates the 2nd run)
    smtcheck_opensmt2t* decider2 = new smtcheck_opensmt2t_lra(sop, "lra checker");
    smt_summary_storet * store2 = new smt_summary_storet(decider2);

    std::vector <std::string> summary_files;
    summary_files.push_back(summary_file);

    if (!summary_files.empty()) {
        store2->deserialize(summary_files);
    }

//get the summaries from both stores based on a particular ID
    itpt& itp1 = store1->find_summary(sum_ID1);
    itpt& itp2 = store2->find_summary(sum_ID1);

    auto res = itp2.equals(&itp1);
    ASSERT_TRUE(res);
    //deletes summary FILE from build/bin/
    std::remove("__summaries");
}

//alternative approach: for given func, ask the ID, then ask its ITP
// summary_idt sum_ID2 = store2->get_summariesID(fun)[0];
// itpt& itp2 = store2->find_summary(sum_ID2);