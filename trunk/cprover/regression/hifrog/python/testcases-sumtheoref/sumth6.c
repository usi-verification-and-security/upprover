 int func(int a, int b)
  {
    int m = 1;
    for (int i = 0; i < 10; i++)
    {
      m = m + (a + b * a);
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
    assert (p*p >= 0);
    int q = func(c, d);
    assert(p == q);
    assert(p + q <= 2);
    return 0;
  }
