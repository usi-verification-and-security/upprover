void main()
{
    unsigned int y = nondet()+1;   

    unsigned int z = y % y;
    assert(z == 0);
}
