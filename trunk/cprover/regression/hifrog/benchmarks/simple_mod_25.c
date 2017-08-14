void main()
{
    int y = nondet();

    unsigned int z = y % y;
    assert(z == 0);
}
