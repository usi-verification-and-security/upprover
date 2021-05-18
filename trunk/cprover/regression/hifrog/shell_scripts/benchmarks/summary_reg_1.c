int a;

void max(int n)
{
  if (n > a) {
     a = n;
  }
}

int nondet_int();

void main(void)
{
  a = 0;
  int p = nondet_int();
  __CPROVER_assume(p <= 100);
  __CPROVER_assume(p >= 10);


  max (p);

  assert (a > 0);
}
