int nondet();
//int mod(int a, int n); // { return _modd(a,n);}
void main()
{
    int y = nondet();
    __CPROVER_assume(y > 0);

    unsigned int z = mod(y,y);
    assert(z == 0);
}
