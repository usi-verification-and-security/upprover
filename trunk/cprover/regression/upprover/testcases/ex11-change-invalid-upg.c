int a;
int b;

void change(){
  a = a + 20;
}

void main(void){
  a = 10;//getchar();
  b = a;

  change();
  assert(a == b + 1);
}

