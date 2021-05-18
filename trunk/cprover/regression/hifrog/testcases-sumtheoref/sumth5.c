int nondet();

int func(int a, int b)
{
    int m = 1;
    int i;
    for (i = 0; i < 10; i++)
    {
        m = m * (a + b);
    }
    int m = m % 2; 
    if (m) 
        return (m-1)* a * b ;
    else 
        return m * a * b;
}

int main()
{
    unsigned int a = nondet();
    unsigned int b = nondet();
    int c = a;
    int d = b;
    int p = func(a, b);
    assert (p * a == 0);
    int q = func(c, d);
    assert(p == q);
    assert(p + q <= 2);
}