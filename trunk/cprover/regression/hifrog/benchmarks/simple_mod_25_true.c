void main()
{
    unsigned int y = nondet();
   __CPROVER_assume(y > 0);   

    unsigned int z = y % y;
    assert(z == 0);
}
