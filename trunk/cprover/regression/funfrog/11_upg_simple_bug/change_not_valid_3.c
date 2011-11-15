int a;
int b;

void change(){
  a++;
}

void main(void){
  a = 10;//getchar();
  b = a;

  change();
  assert(a == b + 1);
}

