int nondet();
int mod_Cd(int a, int n) { return _modd(a,n);}
void main()
{
    int y = nondet();

    unsigned int z = _modd(y,5);
    __CPROVER_assume(mod_Cd(y,5) == z);
    assert(z == 0);
}

