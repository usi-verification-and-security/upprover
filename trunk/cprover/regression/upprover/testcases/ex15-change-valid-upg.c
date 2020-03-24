int nondet_int();

int getchar() {
  int x = nondet_int(); 
  __CPROVER_assume(x < 100);
  __CPROVER_assume(x > 0);
  return x;
}

int a;
int b;

int f1(int c){
  return c+2;
}

void main(void){
  a = getchar();

  b = f1(a);//a+2
  a++;      //a+1

  assert(a == b - 1);
}

