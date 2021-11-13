int a;
int b;

void C(){
  a = b + 1;
}

void B(){ //arg a; B is marked inlined since summary of old B doesn't match anymore, but C still can use its summary till end
  C();
}

void A(){
  a = 0;
  b = 0;
  B(); //B inline, but summary of C can be used.
}

void main(void){
  A();
  assert(a == b + 1);
}

