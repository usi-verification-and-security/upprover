int nondet_int();

void main(void)
{

  int p = nondet_int();
  int q = nondet_int();

  int a = q;
  int b = q;

  __CPROVER_assume(p <= 100);
  __CPROVER_assume(p >= -100);

  if ( nondet_int()) {
     a = p;
  } else {
     b = p;
  }
  
  assert(a + b == p + q);
  //assert (a == 1 || b == 1);
}
