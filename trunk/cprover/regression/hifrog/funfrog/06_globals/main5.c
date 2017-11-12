int a = -101;
int b = 101;

int test(int m, int n)
{
  return m*n;
}

int test1 (int n)
{
  int m = test (n, n);
  return m;
}

void test2(int n)
{
  int m = test1(n) + 1;
  if (m > a) {
     a = m;
  }
}

void  test3(int n)
{
  int m = 0 - (1 + test1(n));
  if (m < b) {
     b = m;
  }
}

int nondet_int();

void main(void)
{
//  a = -101;
//  b = 101;
  int p = nondet_int();
  int q = nondet_int();
  __CPROVER_assume(p <= 100);
  __CPROVER_assume(p >= -100);
  __CPROVER_assume(q <= 100);
  __CPROVER_assume(q >= -100);

  test2 (p);
//  assert (a > 0);
  test3 (q);
//  assert (b < 0);
//  int c = test (a, b);
  assert (b < a);
}
