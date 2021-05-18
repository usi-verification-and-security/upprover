int nondet();
int foo(int a, int n)
{
    unsigned int x = nondet();
    if(a==n)
      __CPROVER_assume(x==0);
    return x;
}
void main()
{
    int y = nondet();

    unsigned int z = foo(y,y);
    assert(z == 0);
}

