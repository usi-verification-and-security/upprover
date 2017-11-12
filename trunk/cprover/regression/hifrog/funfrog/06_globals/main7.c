int a[2];// = 0;

void max(int n)
{
  if (n > 0) {
     a[0] = 1;
  } else {
     a[1] = 1;
  }
}

int count(){
  return a[0] + a[1];
}

int nondet_int();

void main(void)
{
  a[0] = 0;
  a[1] = 0;
  int p = nondet_int();
  __CPROVER_assume(p <= 100);
  __CPROVER_assume(p >= -100);


  max (p);
  int s = count();
  assert (s > 0);
  
  // assert (a[0] == 1 || a[1] == 1);
}
