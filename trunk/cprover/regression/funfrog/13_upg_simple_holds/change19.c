int nondet_int();

int getchar() {
  int x = nondet_int(); 
  __CPROVER_assume(x < 100);
  __CPROVER_assume(x > 0);
  return x;
}

int a;
int b;
int g;

int f0(){
  g = 0;
}

int f1(int c){
  return c-1;
}

void main(void){
  b = getchar();
  f0();
  a = f1(b);

  assert(a == b - 1);
}

