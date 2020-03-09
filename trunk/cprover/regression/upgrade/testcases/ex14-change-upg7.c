__inline int nondet_int();

__inline int getchar() {
  int x = nondet_int(); 
  __CPROVER_assume(x < 95);
  __CPROVER_assume(x > 0);
  return x;
}

int a;
int b;

__inline void f1(){
  a--;
}

__inline void f2(){
  a++;
}

__inline void change(){
  f1();
  f2();
}

void main(void){
  a = getchar();
  b = a;

  change();
  assert(a == b);
}

