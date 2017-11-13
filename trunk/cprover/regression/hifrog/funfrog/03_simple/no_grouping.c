int nondet_int();

//int a;
//int b;

int getchar() {
  int x = nondet_int(); 
  __CPROVER_assume(x < 100);
  __CPROVER_assume(x > 0);
  return x;
}

int f ;

void do_inc(){
  f++;
}

void do_dec(){
  f--;
}

void test1(int c){
  if (f > 0){
    do_dec();
  }
  assert (c >= 0);
}

void test3(int c){
  if (f == 0){
    do_inc();
  }
  test1 (c);
}

void test2(int d){
  do_inc();
  do_dec();
  assert(d + f < 100);
}


void dummy(){
  do_inc();
}

void main(void){
  f = 0;
  int a = 10;//getchar();
  int b = 20;//getchar();
  test2(a);
  test1(a);
  dummy();
  test3(b + f);
  dummy();
  test1(a + f);
  dummy();
  test3(b + f);

//  test2(b);
  int m = (a + b)/2;
  test2(m);
}
