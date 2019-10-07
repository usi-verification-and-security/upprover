int a;
int b ;

void A(){
  a = 0;
}

void B(){
  b = a;
}

void C(){
  a = b + 1;
}

void M(){
  A();
  B();
  C();
}

void main(void){
  M();

  assert(a == b + 1);
}

