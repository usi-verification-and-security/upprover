/*strange behaviour of cprover assumption*/

int x = 0;
int y = 0;

int sqrt(/*int a, int b*/)
{
/*  if (a > 0){
     x++;
  }
  if (b > 0){
     y++;
  }*/
 // x++;
  return x + 1;
}

int sqrt1(int a){
  __CPROVER_assume(a < 0); // it affects the satisfiability of assertion
  x--;
  y--;
  return 0;
}

int nondet_int();

void main(void)
{
/*  int a = nondet_int();
  int b = nondet_int();

  __CPROVER_ASSUME (a > 0);
  __CPROVER_ASSUME (b > 0);
  __CPROVER_ASSUME (a < 100);
  __CPROVER_ASSUME (b < 100);
*/
  int v = sqrt(/*a, b*/);
  int w = sqrt1(v);
  assert(x == 1);  // doesn't work
  //assert(w == 0);    // works
}
