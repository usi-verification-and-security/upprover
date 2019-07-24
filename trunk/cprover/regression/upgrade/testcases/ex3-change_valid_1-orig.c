int nondet_int();

int getchar() {
  int x = nondet_int(); 
  __CPROVER_assume(x < 100);
  __CPROVER_assume(x > 0);
  return x;
}

int a;
int b;

void f(){
  a++;
}

void change(){
  f();
}

void main(void){
  a = getchar();
  b = a;

  change();
  assert(a == b + 1);
}

