int a;
int b ;

void C(){
  a = b + 1;
}

void B(){
  b = a;
  C();
}

void A(){
  a = 0;
  B();
}

void M(){
  A();
}

void main(void){
  M();

  assert(a == b + 1);
}
