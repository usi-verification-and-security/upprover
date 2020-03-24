int a;
int b;

void C(){
  a = b + 1;
}

void B(){
  C();
}

void A(){
  a = 0;
  b = 0;
  B();
}

void main(void){
  A();
  assert(a == b + 1);
}

