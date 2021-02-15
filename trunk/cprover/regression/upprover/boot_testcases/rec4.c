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
  count = nondet_int();
  __CPROVER_assume(count > 5 && count < 10);
  rec();
  assert(a == count);
}
