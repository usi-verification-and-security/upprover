
unsigned int nondetUInt();

int plus2(int a){
 return a +2;    //a=1..11
}

int minus2(int b){
  return b - 2;
}

int add(int a, int b){
  return a + b;
}

void main(){
int a = nondetUInt;
int b = nondetUInt;
    __CPROVER_assume(a>0);
    __CPROVER_assume(a<10);

  b = plus2(a);
  b = minus2(b);
  a = add(a,b);
  assert(a > b) ;
}

