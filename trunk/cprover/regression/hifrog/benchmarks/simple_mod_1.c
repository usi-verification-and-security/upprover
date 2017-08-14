int nondet();
int mod_Cd(int a, int n)
{
    unsigned int x = _modd(a,n);
    if(a==n)
      __CPROVER_assume(x==0);
    return x;
}
void main()
{
    int y = nondet();

    unsigned int z = _modd(y,y);
    __CPROVER_assume(mod_Cd(y,y) == z);
    assert(z == 0);
}
