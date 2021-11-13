int a;
int b;

void C(){
  a = b + 1;
}

void B(){ //arg: b
  b = a;
}

void A(){
  a = 0;
}

void main(void){
  A();
  B();
  C();
  assert(a == b + 1);
}

