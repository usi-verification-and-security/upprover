
void main(){

int a,b;
int m,n;

a = nondet_byte();
b = nondet_byte();

__CPROVER_assume (a > 0 && b > 0 && a < 5 && b < 5);

m = 0;

for (n = b; n >= a; n = n - a){
  m++;
}

assert(b == m * a + n);
}
