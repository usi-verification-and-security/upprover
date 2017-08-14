int nondet();
int mod_Cd(int a, int n) { return _modd(a,n);}
void main()
{
    int y = nondet();

    unsigned int z = _modd(y,y);
    __CPROVER_assume(mod_Cd(y,y) == z);
    assert(z == 0);
}
