// Test: nondet_symex constant is created correctly
int nondet();
void main()
{
    int y = nondet();

    unsigned int z = foo(y,y);
    unsigned int x = foo(y,y);
    assert(z == x);
}
