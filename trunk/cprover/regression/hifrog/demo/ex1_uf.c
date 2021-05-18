int prod(int a, int b)
{
    int p = 1;
    int i;
    for (i = 0; i < 3; i++)
    {
        p = p * (a + b);
    }
    return p;
}

int main(int argc, char** argv)
{
    int a = nondet();
    int b = a;
    int c = a;
    int d = a;
    int q = prod(a, b);
    int p = prod(c, d);
    printf("p: %d; q: %d\n", p, q);
    assert(p == q);
}

