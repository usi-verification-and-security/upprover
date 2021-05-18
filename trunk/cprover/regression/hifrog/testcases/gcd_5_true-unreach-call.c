// Mod lattice - trace only here

int mod_C3(int a, int n) {}
int mod_C4(int a, int n) {}
int mod_Ck(int a, int n) {}
int mod_Cc(int a, int n) {}
int mod_Cd(int a, int n) {}
int mod_Cf(int a, int n) {}
int mod_Cg(int a, int n) {}
int mod_Ch(int a, int n) {}
int mod_C2not(int a, int n) {}
int call__modd(int a, int n) {
   int ret = _modd(a,n);
   //int ret = a % n;
    __CPROVER_assume(mod_C3(a,n) == ret);
    __CPROVER_assume(mod_C2not(a,n) == ret);
    __CPROVER_assume(mod_C4(a,n) == ret);
    __CPROVER_assume(mod_Ck(a,n) == ret);
    __CPROVER_assume(mod_Cc(a,n) == ret);
    __CPROVER_assume(mod_Cf(a,n) == ret);
    __CPROVER_assume(mod_Cg(a,n) == ret);
    __CPROVER_assume(mod_Ch(a,n) == ret);
    __CPROVER_assume(mod_Cd(a,n) == ret);

	return ret;
}

int main()
{
    long x;
    long y;
    long g;

    x = 63;
    y = 18;
    g = 9;

    assert(call__modd(0,g) == 0);
    assert(call__modd(g,g) == 0);
    assert(call__modd(x,g) == 0);
    assert(call__modd(y,g) == 0);

    return 0;
}
