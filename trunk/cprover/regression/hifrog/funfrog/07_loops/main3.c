int nondet_int();

int a;
int b;

int getchar() {
  int x = nondet_int(); 
  __CPROVER_assume(x < 100);
  __CPROVER_assume(x > 0);
  return x;
}

void change0(){
  b++;
}

void change1(){
  b--;
}

void main(void){
  int c = getchar();
  a = 5;
  b = 0;
  for (int i = 0; i < 10; i++){
    if (i < a){
      change0();
    }
    if (a == i){
      assert(b == a);
    }
    if (i >= a){
      change1();
    }
  }
  assert (a != b);
}
