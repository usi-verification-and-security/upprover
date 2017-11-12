int nondet_int();

void main(void)
{

  int p = nondet_int();

  int a = 0;

  __CPROVER_assume(p <= 100);
  __CPROVER_assume(p > 3);

  if (nondet_int()) {
     a = p;
  } 
  
  assert(a != 1);

}
