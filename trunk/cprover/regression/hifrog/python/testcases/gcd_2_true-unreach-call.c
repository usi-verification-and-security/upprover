extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern char __VERIFIER_nondet_char(void);

// Mod lattice - trace only here
int mod_C2not(int a, int n) { return _modd(a,n);}
int mod_C3(int a, int n) { return _modd(a,n);}
int mod_C4(int a, int n) { return _modd(a,n);}
int mod_Ck(int a, int n) { return _modd(a,n);}
int mod_Cc(int a, int n) { return _modd(a,n);}
int mod_Cf(int a, int n) { return _modd(a,n);}
int mod_Cg(int a, int n) { return _modd(a,n);}
int mod_Ch(int a, int n) { return _modd(a,n);}


void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
signed char gcd_test(signed char a, signed char b)
{
    signed char t;

    if (a < (signed char)0) a = -a;
    if (b < (signed char)0) b = -b;

    while (b != (signed char)0) {
        t = b;
        //b = a % t; // orig: a % b
 	b = mod(a,t);
	__CPROVER_assume(mod_C2not(a,t) == b);
	__CPROVER_assume(mod_C3(a,t) == b);
	__CPROVER_assume(mod_C4(a,t) == b);
	__CPROVER_assume(mod_Ck(a,t) == b);
	__CPROVER_assume(mod_Cc(a,t) == b);
	__CPROVER_assume(mod_Cf(a,t) == b);
	__CPROVER_assume((mod_Cg(a,t) == b) && (mod_Ch(a,t) == b));
        a = t;
    }
    return a;
}


int main()
{
    signed char x = __VERIFIER_nondet_char();
    signed char y = __VERIFIER_nondet_char();
    signed char g;

    g = gcd_test(x, y);

    if (y > (signed char)0) {
        __VERIFIER_assert(y >= g);
    }

    return 0;
}
