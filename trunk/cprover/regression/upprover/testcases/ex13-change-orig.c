
int nondet_int();

int get_even(int a, int b){
  int rnd = 0;  
  if (a > 5 || b < 5){
    rnd = a;
  } else {
    rnd = b;
  }
  return rnd;
}

int test1(int a){
  return get_even(a, 5);
}

int test2(int a){
  return get_even(5, a);
}

void main(void)
{

  int a = nondet_int();

  int a1 = test1(a);
  int a2 = test2(a);

  assert(a1 == a2);

}
// In C itself the correct behavior is a1=a2
// but in LRA since cprover does optimization
// x > c --> x >= c+1
// for e.g., in the following c program contains integer
// int x;
// if (x>0)
//  assert(x>=1); in C itself, and Propositional logic safe
            //in LRA it is unsafe because of different nature of LRA that does not know integer, it considers it as Real: so x= 0.5 cex is reported!
