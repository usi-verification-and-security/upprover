/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   facts.h
 * Author: karinek
 *
 * Created on 31 August 2017, 11:01
 */

#ifndef FACTS_H
#define FACTS_H

#include <map>

#include <string>
using namespace std;

class factst {
public:
  virtual bool load_facts(std::string file_name)=0; 
  virtual std::string get_declare_original_function()=0;
  virtual std::string get_original_function_name()=0;
  virtual std::string get_original_header_function()=0;
  virtual bool is_return_value_unsigned()=0;
  virtual std::string get_params_set_of_function()=0;
  
  map<std::string,std::string>::const_iterator 
        get_itr_facts() const { return facts.begin(); }
  map<std::string,std::string>::const_iterator 
        get_itr_end_facts() const { return facts.end(); }
  
protected:
  std::map<std::string,std::string> facts; // facts name, fact encoding: mod_C3, <= 0 |mod_C3::n!0|

};

#endif /* FACTS_H */

