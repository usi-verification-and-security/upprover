int a = 0 , b = 0 , c = 0;

int phi5 (int n){
	a = a + b;
	assert(n>=2);
	return n+ 1;
}

int phi4(int n , int k){
	n += 3;
	c = n + c;
	return n - k + c; 
}

int phi3(int n){
	int m=phi5(n);
	a++;
	m = phi4 (n , m);
	assert(m > 1);
	return m + c + 1;
}

int phi2(int n , int k){
	n *= 3;
	a++;
	return n + k - a; 
}

int phi1(int n) {
	int k = phi3(n+1);
	a++;
	b++;
	c = a + b;
	k = phi2(n , k);
	assert(k>0);
	return k+ c + 1;
}

void main(){
	int n = 1;
	int m = phi1(n);
	//int m2=f(n);
	//assert(m>0);
}


/*
call tree
		O	main
		|
	    O	phi1
		|
		O	phi3 phi2 
		|
		O	phi5 phi4

*/