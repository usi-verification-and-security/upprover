int nondet_int();

int getchar() {
  int x = nondet_int(); 
  __CPROVER_assume(x < 100);
  __CPROVER_assume(x > 0);
  return x;
}

int a;
int b;
int c;

void f1(){
  a++; a++;
  b--; a--;
}

void main1(void){
  a = getchar();
  b = a;
  c = a;

  f1();

}

void main(void){
  main1();

  assert(a == c + 1);
}

