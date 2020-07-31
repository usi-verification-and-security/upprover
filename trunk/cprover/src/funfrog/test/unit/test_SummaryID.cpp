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
//      get convertor from decider
//      auto* convertor = decider1->get_convertor();
//      FlaRef ref = convertor->convert_bool_expr(comp);
//      (void) ref;
        PTRef summary_temp1 = decider1->expression_to_ptref(comp);
        //manually fill newitp1 object
        newitp1->setInterpolant(summary_temp1);
        newitp1->setDecider(decider1);
        newitp1->getTempl().addArg(decider1->expression_to_ptref(x));
        newitp1->getTempl().setBody(summary_temp1);
        
        sum_ID1 = store1->insert_summary(newitp1, fun);
//      insert_summary passes the ownership to summary_store, don't use *new_itp anymore
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
 Test sumID preservation for two summaries for the same functionin in EUF
 Interpolant1 (= a 0)
 Interpolant1 (= a 1)
********************************************************************/
TEST(test_IDequality, test_IDequality_serialize_deserialize_uf_twoSum) {
    
    solver_optionst sop;
    smtcheck_opensmt2t_uf* decider1 = new smtcheck_opensmt2t_uf(sop, "uf checker");
    smt_summary_storet * store1 = new smt_summary_storet(decider1);
    
    std::string fun{"alfa"};
    
    summary_idt sum_ID1;
    summary_idt sum_ID2;
    
    {
//1st Itp
        smt_itpt *newitp1 = new smt_itpt();
//create cprover expression
        symbol_exprt a("a", typet(ID_integer));
        constant_exprt zero(ID_0, typet(ID_integer));
// a == 0
        binary_relation_exprt comp1(a, ID_equal, zero);
//create a PTRef for the expression
        PTRef summary_temp1 = decider1->expression_to_ptref(comp1);
//manually fill the newitp1
        newitp1->setInterpolant(summary_temp1);
        newitp1->setDecider(decider1);
        newitp1->getTempl().addArg(decider1->expression_to_ptref(a));
        newitp1->getTempl().setBody(summary_temp1);
        
        sum_ID1 = store1->insert_summary(newitp1, fun);

//2nd Itp
        smt_itpt *newitp2 = new smt_itpt();
//create another cprover expression
//symbol_exprt b("b", typet(ID_integer));
        constant_exprt one(ID_1, typet(ID_integer));
// a == 1
        binary_relation_exprt comp2(a, ID_equal, one);
        PTRef summary_temp2 = decider1->expression_to_ptref(comp2);
//manually set up the itp
        newitp2->setInterpolant(summary_temp2);
        newitp2->setDecider(decider1);
        newitp2->getTempl().addArg(decider1->expression_to_ptref(a));
        newitp2->getTempl().setBody(summary_temp2);
//debug
//      char *s2 = decider1->getLogic()->printTerm(newitp2->getInterpolant());
//      std::cout << "Interpolant1 " << s2 << '\n';
        
        sum_ID2 = store1->insert_summary(newitp2, fun);
    }


//serialization
    const std::string& summary_file = "__summaries";
    std::ofstream out;
    out.open(summary_file.c_str());
    store1->serialize(out);
    out.close();

//create resources again (simulates the 2nd run)
    smtcheck_opensmt2t* decider2 = new smtcheck_opensmt2t_uf(sop, "uf checker");
    smt_summary_storet * store2 = new smt_summary_storet(decider2);
    
    std::vector <std::string> summary_files {summary_file};
    store2->deserialize(summary_files);


    std::string original_sum1;
    std::string original_sum2;
    {
        std::stringstream ss1;
        store1->find_summary(sum_ID1).serialize(ss1);
        original_sum1 = ss1.str();
        std::stringstream ss2;
        store1->find_summary(sum_ID2).serialize(ss2);
        original_sum2 = ss2.str();
    }

    std::string deserialized_sum1;
    std::string deserialized_sum2;
    {
        std::stringstream ss1;
        store2->find_summary(sum_ID1).serialize(ss1);
        deserialized_sum1 = ss1.str();
        std::stringstream ss2;
        store2->find_summary(sum_ID2).serialize(ss2);
        deserialized_sum2 = ss2.str();
    }

    // MB: weaker, but sufficient check: The first summary contains 0 (and not 1), as it is a == 0
    //     The second summary contains 1 (and not 0), as it is a == 1
    ASSERT_TRUE(original_sum1.find('0') != std::string::npos && deserialized_sum1.find('0') != std::string::npos
    && original_sum2.find('0') == std::string::npos && deserialized_sum2.find('0') == std::string::npos);
    ASSERT_TRUE(original_sum2.find('1') != std::string::npos && deserialized_sum2.find('1') != std::string::npos
                && original_sum1.find('1') == std::string::npos && deserialized_sum1.find('1') == std::string::npos);

    std::remove(summary_file.c_str());
    delete decider1;
    delete decider2;
    delete store1;
    delete store2;
}

/********************************************************************
 Test sumID preservation for two artificial summaries in LRA
  (<= 0 a)
  (<= 1 a)
********************************************************************/
TEST(test_IDequality, test_IDequality_serialize_deserialize_lra_twoSum) {
    
    solver_optionst sop;
    smtcheck_opensmt2t_lra* decider1 = new smtcheck_opensmt2t_lra(sop, "lra checker");
    smt_summary_storet * store1 = new smt_summary_storet(decider1);
    
    std::string fun{"beta"};
    
    summary_idt sum_ID1;
    summary_idt sum_ID2;
    
    {
//1st Itp
        smt_itpt *newitp1 = new smt_itpt();
        unsignedbv_typet bvtype(32);
        //create cprover expression
        symbol_exprt a("a", bvtype);
        constant_exprt zero(ID_0, bvtype);
        // a >= 0
        binary_relation_exprt comp1(a, ID_ge, zero);
        //create a PTRef for the expr
        PTRef summary_temp1 = decider1->expression_to_ptref(comp1);
        //manually set up the itp
        newitp1->setInterpolant(summary_temp1);
        newitp1->setDecider(decider1);
        newitp1->getTempl().addArg(decider1->expression_to_ptref(a));
        newitp1->getTempl().setBody(summary_temp1);
        
        sum_ID1 = store1->insert_summary(newitp1, fun);
//      auto& summary1 = static_cast<smt_itpt&>(store1->find_summary(sum_ID1));

//2nd Itp
        smt_itpt *newitp2 = new smt_itpt();
//create another cprover const expression
        constant_exprt one(ID_1, bvtype);
// a >= 1
        binary_relation_exprt comp2(a, ID_ge, one);
        PTRef summary_temp2 = decider1->expression_to_ptref(comp2);
//manually set up the Itp
        newitp2->setInterpolant(summary_temp2);
        newitp2->setDecider(decider1);
        newitp2->getTempl().addArg(decider1->expression_to_ptref(a));
        newitp2->getTempl().setBody(summary_temp2);
        
        sum_ID2 = store1->insert_summary(newitp2, fun);
// auto& summary2 = static_cast<smt_itpt&>(store1->find_summary(sum_ID2));
        char *s2 = decider1->getLogic()->printTerm(newitp2->getInterpolant());
        std::cout << "Interpolant2  " << s2 << '\n';
    }

//serialization
    const std::string& summary_file = "__summaries";
    std::ofstream out;
    out.open(summary_file.c_str());
    store1->serialize(out);
    out.close();

//create resources again (simulates the 2nd run)
    smtcheck_opensmt2t* decider2 = new smtcheck_opensmt2t_lra(sop, "lra checker");
    smt_summary_storet * store2 = new smt_summary_storet(decider2);
    
    std::vector <std::string> summary_files {summary_file};
    store2->deserialize(summary_files);

    std::string original_sum1;
    std::string original_sum2;
    {
        std::stringstream ss1;
        store1->find_summary(sum_ID1).serialize(ss1);
        original_sum1 = ss1.str();
        std::stringstream ss2;
        store1->find_summary(sum_ID2).serialize(ss2);
        original_sum2 = ss2.str();
    }

    std::string deserialized_sum1;
    std::string deserialized_sum2;
    {
        std::stringstream ss1;
        store2->find_summary(sum_ID1).serialize(ss1);
        deserialized_sum1 = ss1.str();
        std::stringstream ss2;
        store2->find_summary(sum_ID2).serialize(ss2);
        deserialized_sum2 = ss2.str();
    }

    // MB: weaker, but sufficient check: The first summary contains 0 (and not 1), as it is a >= 0
    //     The second summary contains 1 (and not 0), as it is a >= 1
    ASSERT_TRUE(original_sum1.find('0') != std::string::npos && deserialized_sum1.find('0') != std::string::npos
                && original_sum1.find('1') == std::string::npos && deserialized_sum1.find('1') == std::string::npos);
    ASSERT_TRUE(original_sum2.find('1') != std::string::npos && deserialized_sum2.find('1') != std::string::npos
                && original_sum2.find('0') == std::string::npos && deserialized_sum2.find('0') == std::string::npos);

    std::remove(summary_file.c_str());
    delete decider1;
    delete decider2;
    delete store1;
    delete store2;

}

/********************************************************************
 Test the summary with ID 1 in store1 is the same as in store2
 (<= 1 (* (- 1) a))
 true
********************************************************************/
TEST(test_IDequality, test_IDequality_serialize_deserialize_lra_twoSum2) {
    
    solver_optionst sop;
    smtcheck_opensmt2t_lra* decider1 = new smtcheck_opensmt2t_lra(sop, "lra checker");
    smt_summary_storet * store1 = new smt_summary_storet(decider1);
    
    std::string fun{"omega"};
    
    summary_idt sum_ID1;
    summary_idt sum_ID2;
    
    {
        smt_itpt *newitp1 = new smt_itpt();
        unsignedbv_typet bvtype(32);
//create cprover expressions
        symbol_exprt a("a", bvtype);
        constant_exprt one(ID_1, bvtype);
        plus_exprt plus_exp(a, one, bvtype); //plus_exprt(const exprt &_lhs, const exprt &_rhs, const typet &_type)
        constant_exprt zero(ID_0, bvtype);
// a+1 < 0
        binary_relation_exprt comp1(plus_exp, ID_le, zero);
//create PTrefs for exprs
        PTRef summary_temp1 = decider1->expression_to_ptref(comp1); //ptref for full formula
        PTRef a_ptref = decider1->expression_to_ptref(a);     //ptref of arg
    
//manually fill the itp (interpolant, decider, Templ)
        newitp1->setInterpolant(summary_temp1);
        newitp1->setDecider(decider1);
        SummaryTemplate & t1 = newitp1->getTempl();
        t1.setName(fun);
        t1.setBody(summary_temp1);
        t1.addArg(a_ptref);
//insert itp in summary_store and get ID
        sum_ID1 = store1->insert_summary(newitp1, fun);
//debug print
        char *s1 = decider1->getLogic()->printTerm(newitp1->getInterpolant());
        std::cout << "Interpolant1 " << s1 << '\n';

        //create 2nd ITP "true"
        auto * newitp2 = decider1->create_stub_summary(fun);
        //generalize ITP
        std::vector<symbol_exprt> iface_symbols;
        decider1->generalize_summary(newitp2, iface_symbols);
        //store ITP
        sum_ID2 = store1->insert_summary(newitp2, fun);
    }
    
//serialization
    const std::string& summary_file = "__summaries";
    std::ofstream out;
    out.open(summary_file.c_str());
    store1->serialize(out);
    out.close();

//create resources again (simulates the 2nd run)
    smtcheck_opensmt2t* decider2 = new smtcheck_opensmt2t_lra(sop, "lra checker");
    smt_summary_storet * store2 = new smt_summary_storet(decider2);
    
    std::vector <std::string> summary_files {summary_file};
    store2->deserialize(summary_files);
    
    
    std::string original_sum1;
    std::string original_sum2;
    {
        std::stringstream ss1;
        store1->find_summary(sum_ID1).serialize(ss1);
        original_sum1 = ss1.str();
        std::stringstream ss2;
        store1->find_summary(sum_ID2).serialize(ss2);
        original_sum2 = ss2.str();
    }
    
    std::string deserialized_sum1;
    std::string deserialized_sum2;
    {
        std::stringstream ss1;
        store2->find_summary(sum_ID1).serialize(ss1);
        deserialized_sum1 = ss1.str();
        std::stringstream ss2;
        store2->find_summary(sum_ID2).serialize(ss2);
        deserialized_sum2 = ss2.str();
    }
    
    // MB: weaker, but sufficient check: The first summary contains 0 (and not 1), as it is a == 0
    //     The second summary contains 1 (and not 0), as it is a == 1
    ASSERT_TRUE(original_sum1.find('1') != std::string::npos && deserialized_sum1.find('1') != std::string::npos
                && original_sum2.find('a') != std::string::npos && deserialized_sum2.find('a') != std::string::npos);
    
    std::string str ("true");
    
    ASSERT_TRUE(original_sum2.find(str) != std::string::npos && deserialized_sum2.find(str) != std::string::npos
               && original_sum1.find(str) == std::string::npos && deserialized_sum1.find(str) == std::string::npos);
    
    std::remove(summary_file.c_str());
    delete decider1;
    delete decider2;
    delete store1;
    delete store2;
}