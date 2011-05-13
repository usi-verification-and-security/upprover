int test(int a, int b)
{
  return a*b;
}

int test1 (int a)
{
  int b = test (a, a);
  return b;
}

int test2(int a)
{
  int b = test1(a);
  return b+1;
}


int test3(int a)
{
  int b = test1(a);
  return 0 - (1+b);
}

int nondet_int();

void main(void)
{

  int p = nondet_int();
  int q = nondet_int();
  __CPROVER_assume(p <= 100);
  __CPROVER_assume(p >= -100);
  __CPROVER_assume(q <= 100);
  __CPROVER_assume(q >= -100);

  int a = test2 (p);
//  assert (a > 0);
  int b = test3 (q);
//  assert (b < 0);
  assert (b < a);
}
