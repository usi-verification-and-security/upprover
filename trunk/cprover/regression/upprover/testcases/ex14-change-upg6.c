int nondet_int();

int getchar() {
  int x = nondet_int(); 
  __CPROVER_assume(x < 95);
  __CPROVER_assume(x > 0);
  return x;
}

int a;
int b;

extern void f1();

extern void f2();

void change(){
  f1();
  f2();
}

void main(void){
  a = getchar();
  b = a;

  change();
  assert(a == b);
}

