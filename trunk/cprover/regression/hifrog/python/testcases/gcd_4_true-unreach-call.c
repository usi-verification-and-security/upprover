extern void __VERIFIER_error() __attribute__ ((__noreturn__));

extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}

// Mod lattice - trace only here
int mod_C3(int a, int n) {}
int mod_C4(int a, int n) {}
int mod_Ck(int a, int n) {}
int mod_Cc(int a, int n) {}
int mod_Cd(int a, int n) {}
int mod_Cf(int a, int n) {}
int mod_Cg(int a, int n) {}
int mod_C2not(int a, int n) {}
int call__modd(int a, int n) {
	int ret = mod:(a,n);
 	//int ret = a % n;
	__CPROVER_assume(mod_C3(a,n) == ret);
	__CPROVER_assume(mod_C2not(a,n) == ret);
	__CPROVER_assume(mod_C4(a,n) == ret);
	__CPROVER_assume(mod_Ck(a,n) == ret);
	__CPROVER_assume(mod_Cc(a,n) == ret);
        __CPROVER_assume(mod_Cd(a,n) == ret);
	__CPROVER_assume(mod_Cf(a,n) == ret);
	__CPROVER_assume(mod_Cg(a,n) == ret);
	__CPROVER_assume(mod_Cl(a,n) == ret);

	return ret;
}

long gcd_test(long a, long b)
{
    if (a < 0) a = -a;
    if (b < 0) b = -b;

    if (a == 0) {
        return b;
    }

    while (b != 0) {
        if (a > b) {
            a = a - b;
        } else {
            b = b - a;
        }
    }
    return a;
}


int main()
{
    long x;
    long y;
    long g;

    x = 63;
    y = 18;

    g = gcd_test(x, y);

    assert(g == 9); // lra
    assert(call__modd(9,g) == 0); // lra, uf
    assert(call__modd(x,g) == 0); // uf
    assert(call__modd(y,g) == 0); // uf

    return 0;
}
