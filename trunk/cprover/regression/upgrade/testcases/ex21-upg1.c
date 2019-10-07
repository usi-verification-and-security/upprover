
unsigned int nondetUInt();

int plus2(int a){
 return a +2;    
}

int minus2(int b , int a){     //iface change
  a++;    //local change without impact
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
  b = minus2(b , b);
  a = add(a,b);
  assert(a > b) ;
}

