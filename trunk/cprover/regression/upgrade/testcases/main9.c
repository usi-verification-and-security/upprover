/*strange behaviour of cprover assumption*/

int x = 0;
int y = 0;

int sqrt(int a, int b)
{
  if (a*b*b*a > 0){
     x++;
  }
  if (b > 0){
     y*a;
  
 x++;
  return x + 1;
}
}

int sqrt1(int a){
  x--;
  y--;
  return 0;
}

int nondet_int();

void main(void)
{
  int a = nondet_int();
  int b = nondet_int();
  int c = a;
  int d = b;

  __CPROVER_ASSUME (a > 0);
  __CPROVER_ASSUME (b > 0);
  __CPROVER_ASSUME (a < 100);
  __CPROVER_ASSUME (b < 100);

  int v = sqrt(a, b);
  int vv = sqrt(c, d);
  assert(v == vv); 
  
  int ww = sqrt1(c); 
  int w = sqrt1(a);
  assert(w == ww);   

}
