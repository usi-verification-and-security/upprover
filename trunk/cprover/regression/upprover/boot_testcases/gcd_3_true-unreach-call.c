extern void __VERIFIER_error() __attribute__ ((__noreturn__));

extern char __VERIFIER_nondset_char(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}

// Mod lattice - trace only here
int mod_C3(int a, int n) {}
int mod_C4(int a, int n) {}
int mod_Cd(int a, int n) {}
int mod_Cg(int a, int n) {}
int mod_C2not(int a, int n) {}

int call__modd(int a, int n) {
    int ret = _mod(a,n);
    //int ret = a % n;
 
    __CPROVER_assume(mod_C3(a,n) == ret);
    __CPROVER_assume(mod_C2not(a,n) == ret);
    __CPROVER_assume(mod_C4(a,n) == ret);
    __CPROVER_assume(mod_Cd(a,n) == ret);
    __CPROVER_assume(mod_Cg(a,n) == ret);

    return ret;
}

int gcd_test(int a, int b)
{
    signed char t;

    if (a < (signed char)0) a = -a;
    if (b < (signed char)0) b = -b;

    while (b != (int)0) {
        t = b;
        //b = a % b;
 	b = call__modd(a,b);
        a = t;
    }
    return a;
}

int main()
{
    int x = __VERIFIER_nondet_char();
    int y = __VERIFIER_nondet_char();
    int g = gcd_test(x, y);

    if (x > (int)0) {
        assert(x >= g);
    }

    return 0;
}
