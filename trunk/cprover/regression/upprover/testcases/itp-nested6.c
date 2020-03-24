//./hifrog --claim 3 /Users/sepidehasadi/2phd/dev/bench/itp-test/itp-nested6.c --logic qflra
//no summary will be generated! Because claim 3 is inside function C, and function C does not have any inner function Call (Child)

int c2 (int n2){
return n2+1;
}

int b2(int n){
int m2=c2(n);
assert(m2>0);
return m2+1;
}

////////////

int c (int n){
	assert(n>=2);     //claim 3
	return n+1;

}

int b(int n){
int m=c(n);
assert(m>0);
return m+1;
}

int a(int n) {
int k=b(n+1);
assert(k>0);
return k+1;
}

void main(){
int n=1;
int m=a(n);
int mm2=b2(n);
assert(m>0);
assert(mm2 >= 3);
}


/*

main	
|---.
a	b2
|   |
b	c2
|
|
c(asrt3)	   no summary for no one!

*/
