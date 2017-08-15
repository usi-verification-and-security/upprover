int nondet();
int mod_Cd(int a, int n) { return _mod(a,n);}
void main()
{
    int y = nondet();

    unsigned int z = _mod(y,y);
    __CPROVER_assume(mod_Cd(y,y) == z);
    assert(z == 0);
}
