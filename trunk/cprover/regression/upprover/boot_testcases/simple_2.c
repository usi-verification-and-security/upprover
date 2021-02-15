int nondet_int();

int test(int x)
{
  if (x > 0)
    return x+1;
  __CPROVER_assume(0);
}

void main(void)
{
  int x = nondet_int();
  int y = x;

  __CPROVER_assume(x > 0);
  
  x = test(x);

  assert(x != y && x+1 != y);
}
