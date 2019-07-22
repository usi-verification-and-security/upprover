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


/********************************************************************
 This test checks when a given summary is serialized to a FILE,
 and then in the second run gets deserialized from the same FILE,
 the summaryID remains the same.
********************************************************************/
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
//use ID to get back the initial summary(we cannot use the summary pointer(here stub) we passed for storing the summary,
// since summary store requires the ownership of summary)
    itpt& itp1 = store1->find_summary(sum_ID1);
//get the summaries from both stores based on a particular ID
    itpt& itp2 = store2->find_summary(sum_ID1);

    auto res = itp2.equals(&itp1);
    ASSERT_TRUE(res);
    if(res){
        std::cout << "1st test successfully passed!\n" <<'\n';
    }
    //deletes summary FILE from build/bin/
    std::remove("__summaries");
    delete decider2;
}

/********************************************************************
 Test ID preservation for single artificial summary
********************************************************************/
TEST(test_IDequality, test_IDequality_serialize_deserialize_uf) {
    
    solver_optionst sop;
    smtcheck_opensmt2t_uf* decider1 = new smtcheck_opensmt2t_uf(sop, "uf checker");
    smt_summary_storet * store1 = new smt_summary_storet(decider1);
    
    std::string fun{"bar"};
    summary_idt sum_ID1;
    
    {
        smt_itpt *newitp1 = new smt_itpt();
        //create cprover expression using symbol_exprt(name, type)
        symbol_exprt x("x", typet(ID_integer));
        constant_exprt zero(ID_0, typet(ID_integer));
        // x >= 0
        binary_relation_exprt comp(x, ID_ge, zero);
//        get convertor from decider
//        auto* convertor = decider1->get_convertor();
//        FlaRef ref = convertor->convert_bool_expr(comp);
//        (void) ref;
        PTRef summary_temp1 = decider1->expression_to_ptref(comp);
        //manually set the PTRef
        newitp1->setInterpolant(summary_temp1);
        newitp1->setDecider(decider1);
        newitp1->getTempl().addArg(decider1->expression_to_ptref(x));
        newitp1->getTempl().setBody(summary_temp1);
        
        sum_ID1 = store1->insert_summary(newitp1, fun);
        // insert_summary passes the ownership to summary_store, don't use *new_itp anymore
    }
//serialization
    const std::string& summary_file = "__summaries";  //file goes to build/bin/
    std::ofstream out;
    out.open(summary_file.c_str());
    store1->serialize(out);
    out.close();
    delete decider1;

//create resources again (simulates the 2nd run)
    smtcheck_opensmt2t* decider2 = new smtcheck_opensmt2t_uf(sop, "uf checker");
    smt_summary_storet * store2 = new smt_summary_storet(decider2);
    
    std::vector <std::string> summary_files;
    summary_files.push_back(summary_file);
    
    if (!summary_files.empty()) {
        store2->deserialize(summary_files);
    }

    itpt& itp1 = store1->find_summary(sum_ID1);
    itpt& itp2 = store2->find_summary(sum_ID1);
//check if both itps are equal for the same ID
    auto res = itp2.equals(&itp1);
    ASSERT_TRUE(res);
    if(res){
        std::cout << "2nd test successfully passed! \n" <<'\n';
    }
    delete decider2;
    std::remove("__summaries");
}

/********************************************************************
 Test sumID preservation for two artificial summaries in EUF
********************************************************************/
//two summaries for the same function
TEST(test_IDequality, test_IDequality_serialize_deserialize_uf_twoSum) {
    
    solver_optionst sop;
    smtcheck_opensmt2t_uf* decider1 = new smtcheck_opensmt2t_uf(sop, "uf checker");
    smt_summary_storet * store1 = new smt_summary_storet(decider1);
    
    std::string fun{"alfa"};
    
    summary_idt sum_ID1;
    summary_idt sum_ID2;
    
    {
        smt_itpt *newitp1 = new smt_itpt();
        //create cprover expression
        symbol_exprt a("a", typet(ID_integer));
        constant_exprt zero(ID_0, typet(ID_integer));
        // a >= 0
        binary_relation_exprt comp1(a, ID_equal, zero);
        PTRef summary_temp1 = decider1->expression_to_ptref(comp1);
        //manually set the PTRef
        newitp1->setInterpolant(summary_temp1);
        newitp1->setDecider(decider1);
        newitp1->getTempl().addArg(decider1->expression_to_ptref(a));
        newitp1->getTempl().setBody(summary_temp1);
        
        sum_ID1 = store1->insert_summary(newitp1, fun);
        // insert_summary passes the ownership to summary_store, don't use *new_itp1 anymore
        
        char *s1 = decider1->getLogic()->printTerm(newitp1->getInterpolant());
        std::cout << "Interpolant1 " << s1 << '\n';
        
    
        smt_itpt *newitp2 = new smt_itpt();
        //create another cprover expression
        //symbol_exprt b("b", typet(ID_integer));
        constant_exprt one(ID_1, typet(ID_integer));
        // a >= 1
        binary_relation_exprt comp2(a, ID_equal, one);
        PTRef summary_temp2 = decider1->expression_to_ptref(comp2);
        //manually set the PTRef
        newitp2->setInterpolant(summary_temp2);
        newitp2->setDecider(decider1);
        newitp2->getTempl().addArg(decider1->expression_to_ptref(a));
        newitp2->getTempl().setBody(summary_temp2);
        
        sum_ID2 = store1->insert_summary(newitp2, fun);
        // insert_summary passes the ownership to summary_store, don't use *new_itp2 anymore
        
        char *s2 = decider1->getLogic()->printTerm(newitp2->getInterpolant());
        std::cout << "Interpolant2  " << s2 << '\n';
    }

//serialization
    const std::string& summary_file = "__summaries";
    std::ofstream out;
    out.open(summary_file.c_str());
    store1->serialize(out);
    out.close();
    delete decider1;

//create resources again (simulates the 2nd run)
    smtcheck_opensmt2t* decider2 = new smtcheck_opensmt2t_uf(sop, "uf checker");
    smt_summary_storet * store2 = new smt_summary_storet(decider2);
    
    std::vector <std::string> summary_files;
    summary_files.push_back(summary_file);
    
    if (!summary_files.empty()) {
        store2->deserialize(summary_files);
    }
    
    itpt& itpOld1 = store1->find_summary(sum_ID1);
    itpt& itpOld2 = store1->find_summary(sum_ID2);
    
    itpt& itpNew1 = store2->find_summary(sum_ID1);
    itpt& itpNew2 = store2->find_summary(sum_ID2);
    
    auto res2 = itpNew2.equals(&itpOld2);
    ASSERT_TRUE(res2);
    
    auto res1 = itpNew1.equals(&itpOld1);
    ASSERT_TRUE(res1);   //why they have different PTRef?
    
    if(res1 && res2 ){
        std::cout << "3rd test successfully passed!\n" <<'\n';
    }
    std::remove("__summaries");
    delete decider2;
}

/********************************************************************
 Test sumID preservation for two artificial summaries in LRA
********************************************************************/
TEST(test_IDequality, test_IDequality_serialize_deserialize_lra_twoSum) {
    
    solver_optionst sop;
    smtcheck_opensmt2t_lra* decider1 = new smtcheck_opensmt2t_lra(sop, "lra checker");
    smt_summary_storet * store1 = new smt_summary_storet(decider1);
    
    std::string fun{"beta"};
    
    summary_idt sum_ID1;
    summary_idt sum_ID2;
    
    {
        smt_itpt *newitp1 = new smt_itpt();
        //create cprover expression
        symbol_exprt a("a", typet(ID_real));
        constant_exprt zero(ID_0, typet(ID_real));
        // a >= 0
        binary_relation_exprt comp1(a, ID_ge, zero);
        PTRef summary_temp1 = decider1->expression_to_ptref(comp1);
        //manually set the PTRef
        newitp1->setInterpolant(summary_temp1);
        newitp1->setDecider(decider1);
        newitp1->getTempl().addArg(decider1->expression_to_ptref(a));
        newitp1->getTempl().setBody(summary_temp1);
        
        sum_ID1 = store1->insert_summary(newitp1, fun);
        // insert_summary passes the ownership to summary_store, don't use *new_itp anymore
        
        char *s1 = decider1->getLogic()->printTerm(newitp1->getInterpolant());
        std::cout << "Interpolant1 " << s1 << '\n';
        
        
        smt_itpt *newitp2 = new smt_itpt();
        //create another cprover const expression
        constant_exprt one(ID_1, typet(ID_real));
        // a >= 1
        binary_relation_exprt comp2(a, ID_ge, one);
        PTRef summary_temp2 = decider1->expression_to_ptref(comp2);
        //manually set the PTRef
        newitp2->setInterpolant(summary_temp2);
        newitp2->setDecider(decider1);
        newitp2->getTempl().addArg(decider1->expression_to_ptref(a));
        newitp2->getTempl().setBody(summary_temp2);
        
        sum_ID2 = store1->insert_summary(newitp2, fun);
        
        char *s2 = decider1->getLogic()->printTerm(newitp2->getInterpolant());
        std::cout << "Interpolant2  " << s2 << '\n';
    }

//serialization
    const std::string& summary_file = "__summaries";
    std::ofstream out;
    out.open(summary_file.c_str());
    store1->serialize(out);
    out.close();
    delete decider1;

//create resources again (simulates the 2nd run)
    smtcheck_opensmt2t* decider2 = new smtcheck_opensmt2t_lra(sop, "lra checker");
    smt_summary_storet * store2 = new smt_summary_storet(decider2);
    
    std::vector <std::string> summary_files;
    summary_files.push_back(summary_file);
    
    if (!summary_files.empty()) {
        store2->deserialize(summary_files);
    }
    
    itpt& itpOld1 = store1->find_summary(sum_ID1);
    itpt& itpOld2 = store1->find_summary(sum_ID2);
    
    itpt& itpNew1 = store2->find_summary(sum_ID1);
    itpt& itpNew2 = store2->find_summary(sum_ID2);
//check if the associated itp to tehe ID are equal
    
    auto res2 = itpNew2.equals(&itpOld2);
    ASSERT_TRUE(res2);
    
    auto res1 = itpNew1.equals(&itpOld1);
    ASSERT_TRUE(res1);
    
    if(res1 && res2 ){
        std::cout << "4th test successfully passed!\n" <<'\n';
    }
    std::remove("__summaries");
}