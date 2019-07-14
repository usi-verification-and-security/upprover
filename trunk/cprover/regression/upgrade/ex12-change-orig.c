int a;
int b;

int C(){
  a = b + 1;
  return 0;
}

int D(){
  a = b + 1;
  return 0;
}

int E(){
  a = b + 1;
  return 0;
}

int F(){
  a = b + 1;
  return 0;
}

int A(){
  C();
  D();
  return 0;
}

int B(){
  E();
  F();
  return 0;
}

void main(void){
  A();
  B();
  assert(a == b + 1);
}

