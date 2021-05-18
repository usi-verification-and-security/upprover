int prod(int a, int b)
{
    int p = 5;
    int i;
    for (i = 0; i < 2; i++)
    {
        p = p * (a + b);
    }
    return p;
}

int main()
{
    int a = nondet();
    int b = a;
    int c = a;
    int d = a;
    int y = prod(a, b);
    int x = prod(c, d);
    printf("p: %d; q: %d\n", x, y);
//    p++;
  //  q++;
    assert(y == x);
}
