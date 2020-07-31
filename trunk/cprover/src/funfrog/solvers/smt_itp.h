#ifndef SMT_ITP_H
#define SMT_ITP_H

#include "itp.h"

#include <iosfwd>

class smtcheck_opensmt2t;

class SummaryTemplate {
public:
    SummaryTemplate() : body{PTRef_Undef} {}
    ~SummaryTemplate() = default;

    void addArg(PTRef arg) { assert(arg != PTRef_Undef); args.push_back(arg); }
    void setName(const std::string& name_) { name = name_; }
    void setBody(PTRef body_) { assert(body_ != PTRef_Undef); body = body_; }

    const std::vector<PTRef>& getArgs() const { return args; }
    std::string getName() const { return name; }
    PTRef getBody() const { return body; }

private:
    std::string name;
    std::vector<PTRef> args;
    PTRef body;

};

class smt_itpt: public itpt
{
public:
    smt_itpt() : interpolant{PTRef_Undef} {}
    ~smt_itpt() override = default;

    virtual  bool is_trivial() const override { return false; }

    void setDecider(check_opensmt2t *_s);

    SummaryTemplate & getTempl() { return templ; }
    const SummaryTemplate & getTempl() const { return templ; }

    // Serialization
    virtual void serialize(std::ostream& out) const override;

    bool equals(itpt* other) const override;

    // Getters & Setters
    PTRef getInterpolant() const { return interpolant; }
    void setInterpolant(PTRef pt) { interpolant = pt; }

protected:
    // TODO: figure out better way how to store the interpolants
    SummaryTemplate templ;

    smtcheck_opensmt2t *m_decider;

    PTRef interpolant;

};

typedef smt_itpt smt_interpolantt;
#endif
