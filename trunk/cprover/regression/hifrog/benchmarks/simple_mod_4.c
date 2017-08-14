int nondet();
void main()
{
    int y = nondet();

    unsigned int z = _modd(y,y);
    __CPROVER_assume(mod_Cd(y,y) == z);
    assert(z == 0);
}
