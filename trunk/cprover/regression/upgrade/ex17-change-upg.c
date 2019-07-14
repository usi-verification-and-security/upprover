int a;
int b;

int C(){
  a = b + 1;
  return 0;
}

int B(){
  C();
  return 0;
}

int A(){
  a = 0;
  b = 0;
  B();
  return 0;
}

void main(void){
  A();
  assert(a == b + 1);
}

