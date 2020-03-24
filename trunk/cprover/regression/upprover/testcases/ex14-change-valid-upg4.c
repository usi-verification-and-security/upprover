int nondet_int(){};

int getchar() {
  int x = nondet_int(); 
  __CPROVER_assume(x < 50);
  __CPROVER_assume(x > 0);
  return x;
}

int a;
int b;

void f2(){
  a++;
}

void f1(){
  a--;
}

void change(){
  f1();
  f2();
}

void main(){
  a = nondet_int();
  b = a;

  change();
  assert(a == b);
}

