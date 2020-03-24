
int h (int n){
	assert(n>=2);
return n+1;
}

int f(int n){
int m=h(n);
assert(m>1);
return m+1;
}

int g(int n) {
int k=f(n+1);
assert(k>0);
return k+1;
}

void main(){
int new=1;
int m=g(new);
//int m2=f(n);
//assert(m>0);
}


/*
call tree
		O	main
		|
	    O	g
		|
		O	f
		|
		O	h

*/
