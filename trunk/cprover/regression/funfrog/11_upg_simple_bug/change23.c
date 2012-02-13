
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
