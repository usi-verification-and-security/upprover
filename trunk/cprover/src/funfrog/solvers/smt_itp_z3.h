#ifndef SMT_ITP_Z3_H
#define SMT_ITP_Z3_H

#include "itp.h"
#include "smtcheck_z3.h"

#include <iosfwd>

#include <z3++.h>
#include <z3_api.h>
using namespace z3;

class smtcheck_z3t;

class smt_itp_z3t: public itpt
{
public:
    smt_itp_z3t() = default;
    ~smt_itp_z3t() override = default;

    virtual  bool is_trivial() const override { return false; } // if the body is empty or 'true' then it is trivial!

    const std::string getTempl() const {return m_templ;}
    void setTterm(std::string t) { m_templ = t; }
    
    const std::string getArgs() const {return m_args;}
    void setArgs(std::string t) { m_args = t; }
    
    // Getters & Setters
    //z3::expr& getInterpolantExpression() const { return *m_interpolant;}
    //void resetInterpolantExpression() {m_interpolant = new expr(m_decider->parse_expression_from_string("(assert " + m_body + ")", false)); }
    // Creates from string an expression with the summary, we can use with body after substitute!
    
    // Set for constructor purpose only
    void setInterpolant(std::string pt) { m_body = pt; }
    std::string getInterpolant() const { return m_body;}

    // Serialization
    virtual void serialize(std::ostream& out) const override
    {
        assert(m_templ.size() != 0);
        out << m_templ;
    }

    bool equals(itpt* other) const override
    {
        smt_itp_z3t* smt_other = dynamic_cast<smt_itp_z3t*>(other);
        if(!smt_other)
        { return false; }
        return this->getInterpolant() == smt_other->getInterpolant();
    }


protected:
    std::string m_templ=""; // header+body
    std::string m_args=""; // header only
    std::string m_body=""; // Body only
};

#endif
