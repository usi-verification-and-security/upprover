int a;

int nondet_int();

void f(){
  if (a < 1){
    a++;
  }
}

void main(){
  a = 0;
  f();
  assert(a == 1);
}

