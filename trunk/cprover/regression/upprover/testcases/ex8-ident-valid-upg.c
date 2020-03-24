
void main(){

int a,b,m,n;

a = nondet_byte();
b = nondet_byte();

__CPROVER_assume (a > 0 && b > 0 && a < 5 && b < 5);

m = 0;

n = b;

while (n >= a){
  m = m + 1;
  n = n - a;
}

assert(b == m * a + n);
}
