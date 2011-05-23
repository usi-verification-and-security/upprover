int nondet_int();

int a;
int b;

int getchar() {
  int x = nondet_int(); 
  __CPROVER_assume(x < 100);
  __CPROVER_assume(x > 0);
  return x;
}

int test()
{
  a = a + 2;
  b = 1 - b;
  return a + b;
}

void main(void)
{
  a = getchar();
  b = getchar();

  int j = test();
  assert(a>2);
  assert(b<1);
}
