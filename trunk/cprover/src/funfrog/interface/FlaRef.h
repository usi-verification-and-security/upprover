//
// Created by Martin Blicha on 07.09.18.
//

#ifndef PROJECT_FLAREF_H
#define PROJECT_FLAREF_H

#include <solvers/prop/literal.h> // MB: remove when not necessary
/* We needed a unified abstraction for a formula representation:
 * 1) for propositional literalts in Prop-HiFrog (CProver's literalt),
 * 2) for PTRefs in OpenSMT in SMT-HiFrog, and
 * 3) for Z3's expressions.
 *
 * FlaRef is a handle to a boolean term of the underlying solver(OpenSMT, Z3),
 * without the explicit need to know which solver is in use.

 * This Flaref struct has been introduced to extract the general `convertort` interface
 * to replace CProver's literalt


An abstraction used in the interface 'convertort' in convertor.h
*/
struct FlaRef{
    using reft = unsigned;

    FlaRef() : FlaRef(const_no(), false) {}
    FlaRef(reft x) : x{x} {}
    FlaRef(reft no, bool sign) {
        x = (no << 1) | (static_cast<reft>(sign));
    }

    static FlaRef get_true() { return FlaRef_True;}
    static FlaRef FlaRef_True;
    friend inline bool operator==(FlaRef a, FlaRef b) {return a.x == b.x;}

    reft no() const
    {
        return x >> 1;
    }

    bool sign() const
    {
        return x & 1;
    }

    bool is_constant() const
    {
        return no() == const_no();
    }

    static inline reft const_no()
    {
        return (static_cast<reft>(-1)<<1)>>1;
    }

    bool is_true() const
    {
        return is_constant() && sign();
    }

    bool is_false() const
    {
        return is_constant() && !sign();
    }

    FlaRef operator!() const
    {
        return FlaRef(no(), !sign());
    }

protected:
    reft x;
};

// constants
inline FlaRef const_formula(bool value)
{
    return FlaRef(FlaRef::const_no(), value);
}

// MB: ideally these should not be necessary, or at least, they should be present only in SAT
// version; but first we need to modify ssa steps
inline literalt flaref_to_literal(const FlaRef f) { return literalt{f.no(), f.sign()};}
inline FlaRef literal_to_flaref (const literalt l) { return FlaRef{l.var_no(), l.sign()};}

#endif //PROJECT_FLAREF_H
