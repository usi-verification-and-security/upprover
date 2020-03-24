int c (int n){
return n+1;
}

int b(int n){
int m=c(n);
//assert(m>0);
return m+1;
}

int a(int n) {
int k=b(n+1);
//assert(k>0);
return k+1;
}

void main(){
int n=1;
int m=a(n);
//int m2=b(n);
assert(m>0);
}


/*

O	main
|
O	a
|
O	b
|
O	c

*/
