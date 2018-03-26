int a(int n) {
int k=b(n*n);
//assert(k>0);
return k*n;
}

int b(int n){
int m=c(2*n);
//assert(m>0);
return m%n;
}

int c (int n){
return n/2;
}

void main(){
//int n=2;
int n=nondetInt();
if (n < 0 || n > 10) return;
int m=a(2*n);
assert(m>=0);
}
