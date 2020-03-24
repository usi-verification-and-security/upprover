int nondet_int();

int getchar() {
  int x = nondet_int(); 
  __CPROVER_assume(x < 100);
  __CPROVER_assume(x > 0);
  x++;
  return x;
}

int a;
int b;

void print(){ 
printf("hey\n");
}

void nothing(){
  print();
}

void main(void){
  a = getchar();
  b = a;
  b++;
  nothing();
  assert(a + 1 == b );
}

