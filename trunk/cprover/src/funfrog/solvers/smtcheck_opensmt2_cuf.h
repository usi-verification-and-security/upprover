/*******************************************************************\

Module: Wrapper for OpenSMT2

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_OPENSMT2_CUF_H
#define CPROVER_SMTCHECK_OPENSMT2_CUF_H

#include "smtcheck_opensmt2.h"
#include <util/mp_arith.h>

class BitBlaster;

class smtcheck_opensmt2t_cuf : public smtcheck_opensmt2t
{
public:
    smtcheck_opensmt2t_cuf(solver_optionst solver_options, const char* name
    ) :
          smtcheck_opensmt2t(),
          bitwidth(solver_options.m_bitwidth),
          type_constraints_level(solver_options.m_byte_type_constraints)      
    {
        initializeSolver(solver_options, name);
    }

    virtual ~smtcheck_opensmt2t_cuf(); // d'tor

    virtual exprt get_value(const exprt &expr) override;

    virtual PTRef expression_to_ptref(const exprt & expr) override;

    int check_ce(std::vector<exprt>& exprs, std::map<const exprt, int>& model,
                 std::set<int>& refined, std::set<int>& weak, int start, int end, int step, int do_dep);

    bool refine_ce_solo(std::vector<exprt>& exprs, int i); // refine only exprs[i]

    bool refine_ce_mul(std::vector<exprt>& exprs, std::set<int>& is); // refine only subset of expr

    bool force_refine_ce(std::vector<exprt>& exprs, std::set<int>& refined); // refine all from exprs, but already refined

    std::string get_refinement_failure_reason() { return unsupported_info.get_failure_reason(id2string(_fails_type_id)); } 

    virtual SRef get_numeric_sort() const override {return uflogic->getSort_CUFNUM();}

protected:
    BVLogic* bvlogic; // Extra var, inner use only - Helps to avoid dynamic cast!
    CUFLogic* uflogic; // Extra var, inner use only - Helps to avoid dynamic cast!

    BitBlaster* bitblaster;

    unsigned bitwidth;

    int type_constraints_level; // The level of checks in BV logic for numerical checks possible values

    mp_integer max_num; // w.r.t. current bitwidth

    std::map<size_t, PTRef> converted_bitblasted_exprs;

    irep_idt _fails_type_id; // Reason 2 fail of CUF theoref

    virtual PTRef unsupported_to_var(const exprt & expr) override; // for isnan, mod, arrays ect. that we have no support (or no support yet) create over-approx as nondet

    PTRef unsupported2var_bv(const exprt &expr); // for BVs

    virtual void initializeSolver(const solver_optionst solver_options, const char*) override;

    virtual PTRef numeric_constant(const exprt & expr) override;
    
    virtual PTRef new_num_var(const std::string & var_name) override;

    virtual PTRef type_cast(const exprt & expr) override;

    PTRef lconst_bv(const exprt &expr); // For bv only!

    void bindBB(const exprt& expr, PTRef ptl);

    void refine_ce_one_iter(std::vector<exprt>& exprs, int i);
    
    PTRef var_bv(const exprt &expr); // lvar for bv logic

    PTRef get_bv_var(const char* name);

    PTRef get_bv_const(const char* val);

    PTRef convert_bv(const exprt &expr);

    bool convert_bv_eq_ite(const exprt &expr, PTRef& ptl);

    PTRef type_cast_bv(const exprt &expr);

    void add_constraints4chars_bv(const exprt &expr, PTRef &var);

    void add_constraints4chars_bv_char(PTRef &var, const irep_idt type_id_c, const irep_idt type_id);

    void add_constraints4chars_bv_bool(const exprt &expr, PTRef &var, int size, const irep_idt type_id);

    void add_constraints4chars_numeric(PTRef &var, int size, const irep_idt type_id);

    virtual bool is_non_linear_operator(PTRef tr) const override;

    PTRef split_exprs(irep_idt id, vec<PTRef>& args);
    PTRef split_exprs_bv(irep_idt id, vec<PTRef>& args);

    PTRef labs_bv(const exprt &expr); // from convert for ID_abs

};

#endif
