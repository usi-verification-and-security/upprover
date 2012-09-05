int a;
int count;

int nondet_int();

void rec(){
  if (a < count){
    a++;
    rec();
  }
}

void main(){
  a = 0;
  count = 5;//nondet_int();
  //__CPROVER_assume(count > 5 && count < 100);
  rec();
  assert(a < 5);
}
