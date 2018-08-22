int nondet();

int func(int a, int b)
{
    int m = 1;
    int i;
    for (i = 0; i < 10; i++)
    {
        m = m * (a * b * a);
    }
    return (m % 2);
}

int main()
{
    unsigned int a = nondet();
    unsigned int b = nondet();
    int c = a;
    int d = b;
    int p = func(a, b);
    assert (p * p >= 0); //prop
    int q = func(c, d);
    assert(p == q);   //uf

    assert(p + q <= 2);  //prop
}
