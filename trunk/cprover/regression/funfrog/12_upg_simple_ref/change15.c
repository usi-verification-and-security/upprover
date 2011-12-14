int a;
int b;

int A(){
  a = 0;
  return 0;
}

int B(){
  b = a;
  return 0;
}

int C(){
  a = b + 1;
  return 0;
}

void main(void){
  A();
  B();
  C();
  assert(a == b + 1);
}

